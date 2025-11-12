#include <gmp.h>
#include <math.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct
{
    mpz_t n;
    mpz_t x;
} bbs_state;

#define AES_KEY_SIZE 32
#define AES_BLOCK_SIZE 16

int first_primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
                      31, 37, 41, 43, 47, 53, 59, 61, 67,
                      71, 73, 79, 83, 89, 97, 101, 103,
                      107, 109, 113, 127, 131, 137, 139,
                      149, 151, 157, 163, 167, 173, 179,
                      181, 191, 193, 197, 199, 211, 223,
                      227, 229, 233, 239, 241, 251, 257,
                      263, 269, 271, 277, 281, 283, 293,
                      307, 311, 313, 317, 331, 337, 347, 349};

typedef struct
{
    mpz_t n, e, d;

} rsa_context;

typedef struct
{
    bbs_state   bbs;
    rsa_context rsa_key;
    uint8_t     aes_key[32];
    uint8_t     aes_iv[16];
} task_context;

static double now_sec(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

void bbs_init(bbs_state *bbs, size_t bits)
{
    mpz_t           p, q;
    gmp_randstate_t rs;

    mpz_inits(p, q, bbs->n, bbs->x, NULL);
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, time(NULL));

    do
    {
        mpz_urandomb(p, rs, bits / 2);
        mpz_nextprime(p, p);
    } while (mpz_fdiv_ui(p, 4) != 3);

    do
    {
        mpz_urandomb(q, rs, bits / 2);
        mpz_nextprime(q, q);
    } while (mpz_fdiv_ui(q, 4) != 3);

    mpz_mul(bbs->n, p, q);

    mpz_t x0;
    mpz_init(x0);
    mpz_urandomm(x0, rs, bbs->n);

    mpz_powm_ui(bbs->x, x0, 2, bbs->n);

    mpz_clears(x0, p, q, NULL);
    gmp_randclear(rs);
}

void bbs_clear(bbs_state *bbs)
{
    mpz_clears(bbs->n, bbs->x, NULL);
}

void bbs_generate_bits(bbs_state *bbs, uint8_t *bits, size_t n)
{
    for (size_t i = 0; i < n; i++)
    {
        mpz_powm_ui(bbs->x, bbs->x, 2, bbs->n);
        bits[i] = mpz_tstbit(bbs->x, 0);
    }
}

void bits_to_mpz(mpz_t out, const uint8_t *bits, size_t n)
{
    mpz_set_ui(out, 0);
    for (size_t i = 0; i < n; i++)
    {
        mpz_mul_2exp(out, out, 1);
        if (bits[i])
            mpz_add_ui(out, out, 1);
    }
}

int nist_freq_monobit(const uint8_t *bits, size_t n)
{
    long sum = 0;

    for (int i = 0; i < n; i++)
    {
        sum += (bits[i] == 1) ? 1 : -1;
    }

    double s_obs = fabs((double)sum) / sqrt((double)n);
    double p_value = erfc(s_obs) / M_SQRT2;

    printf("Frequency (Monobit) Test:\n");
    printf("  n       = %zu\n", n);
    printf("  sum     = %ld\n", sum);
    printf("  s_obs   = %f\n", s_obs);
    printf("  p-value = %g\n", p_value);
    printf("  Since p_value(%g) is %s than 0.01, this test %s!\n",
           p_value,
           (p_value >= 0.01) ? ">=" : "<",
           (p_value >= 0.01) ? "Passes" : "Fails");

    return (p_value >= 0.01) ? 0 : -1;
}

int nist_runs(const uint8_t *bits, size_t n)
{
    size_t ones = 0;
    for (size_t i = 0; i < n; i++)
    {
        if (bits[i] == 1)
            ones++;
    }
    double pi = (double)ones / (double)n;

    printf("\nRuns Test:\n");
    printf("  n       = %zu\n", n);
    printf("  ones    = %zu\n", ones);
    printf("  pi      = %f\n", pi);

    double t = 2.0 / sqrt((double)n);
    printf("  t       = %f\n", t);
    if (fabs(pi - 0.5) >= t)
    {
        printf("  |pi - 1/2| >= 2/sqrt(n), test not applicable.\n");
        return -1;
    }

    size_t Vn = 1;
    for (size_t i = 1; i < n; i++)
    {
        if (bits[i] != bits[i - 1])
            Vn++;
    }
    printf("  Vn      = %zu\n", Vn);

    double num = fabs((double)Vn - 2.0 * n * pi * (1.0 - pi));
    double den = 2.0 * sqrt(2.0 * n) * pi * (1.0 - pi);
    double p_value = erfc(num / den);

    printf("  p-value = %g\n", p_value);
    printf("  Since p_value(%g) is %s than 0.01, this test %s!\n",
           p_value,
           (p_value >= 0.01) ? ">=" : "<",
           (p_value >= 0.01) ? "Passes" : "Fails");

    return (p_value >= 0.01) ? 0 : -1;
}

#define BLOCK_TO_INT(pos) ({                    \
    int v = 0;                                  \
    for (int i = 0; i < L; i++)                 \
        v = (v << 1) | bits[pos + (L - 1 - i)]; \
    v;                                          \
})

int nist_maurer_universal(const uint8_t *bits, size_t n)
{
    int    L;
    size_t Q, K;

    if (n >= 1059061760)
        L = 16;
    else if (n >= 496435200)
        L = 15;
    else if (n >= 231669760)
        L = 14;
    else if (n >= 107560960)
        L = 13;
    else if (n >= 49643520)
        L = 12;
    else if (n >= 22753280)
        L = 11;
    else if (n >= 10342400)
        L = 10;
    else if (n >= 4654080)
        L = 9;
    else if (n >= 2068480)
        L = 8;
    else if (n >= 904960)
        L = 7;
    else if (n >= 387840)
        L = 6;
    else
    {
        printf("Not enough bits for Maurer test.\n");
        return -1;
    }

    Q = 10u << L;
    K = n / L - Q;

    size_t table_size = 1u << L;
    if (table_size > n)
    {
        fprintf(stderr, "Error: table too large for bitstream\n");
        return -1;
    }

    int *T = calloc(table_size, sizeof(int));
    if (!T)
    {
        perror("calloc");
        return -1;
    }

    size_t pos = 0;
    for (size_t i = 1; i <= Q; i++)
    {
        int idx = BLOCK_TO_INT(pos);
        T[idx] = (int)i;
        pos += (size_t)L;
    }

    double sum = 0.0;
    for (size_t i = Q + 1; i <= Q + K; i++)
    {
        int idx = BLOCK_TO_INT(pos);
        int last = T[idx];
        int distance = (int)i - last; // last must be > 0 because Q >> table_size-ish
        T[idx] = (int)i;
        sum += log2((double)distance);
        pos += (size_t)L;
    }

    free(T);

    double fn = sum / (double)K;

    double expected, variance;
    switch (L)
    {
        case 6:
            expected = 5.2177052;
            variance = 2.954;
            break;
        case 7:
            expected = 6.1962507;
            variance = 3.125;
            break;
        case 8:
            expected = 7.1836656;
            variance = 3.238;
            break;
        case 9:
            expected = 8.1764248;
            variance = 3.311;
            break;
        case 10:
            expected = 9.1723243;
            variance = 3.356;
            break;
        case 11:
            expected = 10.170032;
            variance = 3.384;
            break;
        case 12:
            expected = 11.168765;
            variance = 3.401;
            break;
        case 13:
            expected = 12.168070;
            variance = 3.410;
            break;
        case 14:
            expected = 13.167693;
            variance = 3.416;
            break;
        case 15:
            expected = 14.167488;
            variance = 3.419;
            break;
        case 16:
            expected = 15.167379;
            variance = 3.421;
            break;
        default: expected = 7; variance = 3;
    }

    double c = 0.7 - (0.8 / L) + ((4.0 + 32.0 / L) * pow(K, -3.0 / (double)L) / 15.0);
    double sigma = c * sqrt(variance / (double)K);
    double p_value = erfc(fabs(fn - expected) / (sqrt(2.0) * sigma));

    printf("\nMaurer’s Universal Statistical Test:\n");
    printf("  n = %zu, L = %d, Q = %zu\n", n, L, Q);
    printf("  c = %g, sigma = %g, K = %zu, sum = %g\n", c, sigma, K, sum);
    printf("  fn = %.6f, expected = %.6f\n", fn, expected);
    printf("  Since p_value(%g) is %s than 0.01, this test %s!\n",
           p_value,
           (p_value >= 0.01) ? ">=" : "<",
           (p_value >= 0.01) ? "Passes" : "Fails");

    return (p_value >= 0.01) ? 0 : -1;
}

int miller_rabin(mpz_t n, int rounds)
{
    if (mpz_cmp_ui(n, 3) < 0)
        return 0;
    if (mpz_even_p(n))
        return 0;

    mpz_t n_minus_1, q, a, x, temp;
    mpz_inits(n_minus_1, q, a, x, temp, NULL);

    mpz_sub_ui(n_minus_1, n, 1);
    mpz_set(q, n_minus_1);

    unsigned long k = 0;
    while (mpz_even_p(q))
    {
        k++;
        mpz_divexact_ui(q, q, 2);
    }

    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, time(NULL));

    for (int i = 0; i < rounds; i++)
    {
        mpz_urandomm(a, rs, n_minus_1);
        mpz_add_ui(a, a, 2);
        mpz_powm(x, a, q, n);

        if (mpz_cmp_ui(x, 1) == 0 || mpz_cmp(x, n_minus_1) == 0)
            continue;

        int continue_outer = 0;
        for (unsigned long j = 1; j < k; j++)
        {
            mpz_powm_ui(x, x, 2, n);
            if (mpz_cmp(x, n_minus_1) == 0)
            {
                continue_outer = 1;
                break;
            }
        }

        if (continue_outer)
            continue;

        mpz_clears(n_minus_1, q, a, x, temp, NULL);
        gmp_randclear(rs);
        return 0;
    }

    mpz_clears(n_minus_1, q, a, x, temp, NULL);
    gmp_randclear(rs);
    return 1;
}

int low_level_primality(mpz_t n)
{
    for (int i = 0; i < (sizeof(first_primes) / sizeof(int)); i++)
    {
        if (mpz_cmp_ui(n, first_primes[i]) == 0)
            return 0;

        mpz_t rem;
        mpz_init(rem);

        if (mpz_mod_ui(rem, n, first_primes[i]) == 0)
        {
            mpz_clear(rem);
            return -1;
        }

        mpz_clear(rem);
    }

    return 0;
}

void bbs_generate_prime(bbs_state *bbs, mpz_t n, size_t bits)
{
    int      attempt = 0;
    uint8_t *bitstream = malloc(bits);
    if (!bitstream)
    {
        perror("malloc");
        exit(EXIT_FAILURE);
    }

    while (1)
    {
        attempt++;
        bbs_generate_bits(bbs, bitstream, bits);

        bits_to_mpz(n, bitstream, bits);

        mpz_setbit(n, bits - 1);
        mpz_setbit(n, 0);

        // gmp_printf("#%d: Generated prime candidate: %Zd\n", attempt, n);

        if (low_level_primality(n) == -1)
        {
            // printf("Failed low level primality test\n");
            continue;
        }

        if (miller_rabin(n, 8))
        {
            break;
        }
        // printf("Failed Miller Rabin\n");
    }

    gmp_printf("Found prime after %d attempts\n", attempt);
}

int rsa_key_gen(mpz_t e, mpz_t d, mpz_t n, size_t bits)
{
    bbs_state bbs;
    bbs_init(&bbs, bits);

    mpz_t p, q, phi, gcd;
    mpz_inits(p, q, phi, gcd, NULL);

    bbs_generate_prime(&bbs, p, bits / 2);
    bbs_generate_prime(&bbs, q, bits / 2);

    mpz_mul(n, p, q);

    mpz_t p1, q1;
    mpz_inits(p1, q1, NULL);
    mpz_sub_ui(p1, p, 1);
    mpz_sub_ui(q1, q, 1);
    mpz_mul(phi, p1, q1);
    mpz_clears(p1, q1, NULL);

    mpz_set_ui(e, 65537);

    mpz_gcd(gcd, e, phi);

    if (mpz_cmp_ui(gcd, 1) != 0)
        return -1;

    mpz_invert(d, e, phi);

    printf("RSA key generated:\n");
    gmp_printf("p = %Zd\n\nq = %Zd\n\nn = %Zd\n\ne = %Zd\n\nd = %Zd\n\n", p, q, n, e, d);

    mpz_clears(p, q, phi, gcd, NULL);

    return 0;
}

void bbs_generate_aes_key_256(bbs_state *bbs, uint8_t *key, size_t key_len)
{
    size_t   n = key_len * 8;
    uint8_t *bits = malloc(n);
    if (!bits)
    {
        perror("malloc");
        exit(EXIT_FAILURE);
    }

    bbs_generate_bits(bbs, bits, n);

    for (size_t i = 0; i < key_len; i++)
    {
        uint8_t byte = 0;
        for (int j = 0; j < 8; j++)
        {
            byte = (byte << 1) | bits[i * 8 + j];
        }

        key[i] = byte;
    }

    free(bits);
}

int aes_encrypt_cbc(const uint8_t *key, const uint8_t *iv,
                    const uint8_t *plaintext, int plaintext_len,
                    uint8_t **ciphertext, int *ciphertext_len)
{
    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    if (!ctx)
        return 0;

    int len = 0;
    int out_len = 0;

    *ciphertext = malloc(plaintext_len + EVP_MAX_BLOCK_LENGTH);
    if (!*ciphertext)
    {
        EVP_CIPHER_CTX_free(ctx);
        return 0;
    }

    if (EVP_EncryptInit_ex(ctx, EVP_aes_256_cbc(), NULL, key, iv) != 1)
    {
        EVP_CIPHER_CTX_free(ctx);
        free(*ciphertext);
        return 0;
    }

    if (EVP_EncryptUpdate(ctx, *ciphertext, &len, plaintext, plaintext_len) != 1)
    {
        EVP_CIPHER_CTX_free(ctx);
        free(*ciphertext);
        return 0;
    }
    out_len = len;

    if (EVP_EncryptFinal_ex(ctx, *ciphertext + out_len, &len) != 1)
    {
        EVP_CIPHER_CTX_free(ctx);
        free(*ciphertext);
        return 0;
    }
    out_len += len;

    *ciphertext_len = out_len;

    EVP_CIPHER_CTX_free(ctx);
    return 1;
}

int aes_decrypt_cbc(const uint8_t *key, const uint8_t *iv,
                    const uint8_t *ciphertext, int ciphertext_len,
                    uint8_t **plaintext, int *plaintext_len)
{
    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    if (!ctx)
        return 0;

    int len = 0;
    int out_len = 0;

    *plaintext = malloc(ciphertext_len);
    if (!*plaintext)
    {
        EVP_CIPHER_CTX_free(ctx);
        return 0;
    }

    if (EVP_DecryptInit_ex(ctx, EVP_aes_256_cbc(), NULL, key, iv) != 1)
    {
        EVP_CIPHER_CTX_free(ctx);
        free(*plaintext);
        return 0;
    }

    if (EVP_DecryptUpdate(ctx, *plaintext, &len, ciphertext, ciphertext_len) != 1)
    {
        EVP_CIPHER_CTX_free(ctx);
        free(*plaintext);
        return 0;
    }
    out_len = len;

    if (EVP_DecryptFinal_ex(ctx, *plaintext + out_len, &len) != 1)
    {
        EVP_CIPHER_CTX_free(ctx);
        free(*plaintext);
        return 0;
    }
    out_len += len;

    *plaintext_len = out_len;

    EVP_CIPHER_CTX_free(ctx);
    return 1;
}

static void print_hex(const char *label, const uint8_t *data, size_t len)
{
    printf("%s", label);
    for (size_t i = 0; i < len; i++)
        printf("%02X", data[i]);
    printf("\n");
}

void rsa_encrypt(mpz_t c, const mpz_t m, rsa_context rsa)
{
    mpz_powm(c, m, rsa.e, rsa.n);
}

void rsa_encrypt_key(mpz_t ciphertext, const unsigned char *aes_key, rsa_context rsa_key)
{
    mpz_t m;
    mpz_init(m);
    mpz_import(m, AES_KEY_SIZE, 1, 1, 0, 0, aes_key);

    rsa_encrypt(ciphertext, m, rsa_key);
    mpz_clear(m);
}

void rsa_decrypt(mpz_t m, const mpz_t c, rsa_context rsa)
{
    mpz_powm(m, c, rsa.d, rsa.n);
}

void rsa_decrypt_key(unsigned char *aes_key_out, const mpz_t ciphertext, rsa_context rsa_key)
{
    mpz_t p;
    mpz_init(p);
    rsa_decrypt(p, ciphertext, rsa_key);

    size_t count;
    mpz_export(aes_key_out, &count, 1, 1, 0, 0, p);

    if (count < AES_KEY_SIZE)
        memmove(aes_key_out + (AES_KEY_SIZE - count), aes_key_out, count),
            memset(aes_key_out, 0, AES_KEY_SIZE - count);

    mpz_clear(p);
}

void rsa_decrypt_crt(mpz_t m, const mpz_t c, rsa_context rsa)
{
    mpz_powm(m, c, rsa.d, rsa.n);
}

void rsa_decrypt_key_crt(unsigned char *aes_key_out, const mpz_t ciphertext, rsa_context rsa_key)
{
}

int aes_encrypt_file(const char *in_filename, const char *out_filename,
                     const unsigned char *key, unsigned char *iv)
{
    FILE *infile = fopen(in_filename, "rb");
    FILE *outfile = fopen(out_filename, "wb");
    if (!infile || !outfile)
    {
        perror("fopen");
        return 0;
    }

    RAND_bytes(iv, AES_BLOCK_SIZE);
    fwrite(iv, 1, AES_BLOCK_SIZE, outfile);

    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    EVP_EncryptInit_ex(ctx, EVP_aes_256_cbc(), NULL, key, iv);

    unsigned char inbuf[1024], outbuf[1040];
    int           inlen, outlen;
    while ((inlen = fread(inbuf, 1, sizeof(inbuf), infile)) > 0)
    {
        EVP_EncryptUpdate(ctx, outbuf, &outlen, inbuf, inlen);
        fwrite(outbuf, 1, outlen, outfile);
    }

    EVP_EncryptFinal_ex(ctx, outbuf, &outlen);
    fwrite(outbuf, 1, outlen, outfile);

    EVP_CIPHER_CTX_free(ctx);
    fclose(infile);
    fclose(outfile);
    return 1;
}

int aes_decrypt_file(const char *in_filename, const char *out_filename,
                     const unsigned char *key)
{
    FILE *infile = fopen(in_filename, "rb");
    FILE *outfile = fopen(out_filename, "wb");
    if (!infile || !outfile)
    {
        perror("fopen");
        return 0;
    }

    unsigned char iv[AES_BLOCK_SIZE];
    fread(iv, 1, AES_BLOCK_SIZE, infile);

    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    EVP_DecryptInit_ex(ctx, EVP_aes_256_cbc(), NULL, key, iv);

    unsigned char inbuf[1024], outbuf[1040];
    int           inlen, outlen;
    while ((inlen = fread(inbuf, 1, sizeof(inbuf), infile)) > 0)
    {
        EVP_DecryptUpdate(ctx, outbuf, &outlen, inbuf, inlen);
        fwrite(outbuf, 1, outlen, outfile);
    }

    EVP_DecryptFinal_ex(ctx, outbuf, &outlen);
    fwrite(outbuf, 1, outlen, outfile);

    EVP_CIPHER_CTX_free(ctx);
    fclose(infile);
    fclose(outfile);
    return 1;
}

static void task_1(task_context *ctx)
{
    printf("Task 1:\n");
    rsa_key_gen(ctx->rsa_key.e, ctx->rsa_key.d, ctx->rsa_key.n, 2048);

    bbs_state    bbs;
    mpz_t        p;
    const size_t N_BITS = 1048576;

    bbs_init(&bbs, 1024);
    mpz_init(p);

    uint8_t *bits = malloc(N_BITS);
    if (!bits)
    {
        perror("malloc");
        exit(EXIT_FAILURE);
    }

    printf("Generating %zu random bits using Blum Blum Shub...\n", N_BITS);
    bbs_generate_bits(&bbs, bits, N_BITS);

    int s = nist_freq_monobit(bits, N_BITS);
    int d = nist_runs(bits, N_BITS);
    int t = nist_maurer_universal(bits, N_BITS);
}

static void task_2(task_context *ctx)
{
    printf("\n\nTask 2:\n");

    bbs_generate_aes_key_256(&ctx->bbs, ctx->aes_key, sizeof(ctx->aes_key));

    if (RAND_bytes(ctx->aes_iv, sizeof(ctx->aes_iv)) != 1)
    {
        fprintf(stderr, "RAND_bytes failed\n");
        return;
    }

    const char *message = "This is the plaintext message to be encrypted!";
    int         plaintext_len = (int)strlen(message);

    uint8_t *ciphertext = NULL;
    int      ciphertext_len = 0;

    if (!aes_encrypt_cbc(ctx->aes_key, ctx->aes_iv, (const uint8_t *)message,
                         plaintext_len, &ciphertext, &ciphertext_len))
    {
        fprintf(stderr, "Encryption failed\n");
        return;
    }

    uint8_t *decrypted = NULL;
    int      decrypted_len = 0;

    if (!aes_decrypt_cbc(ctx->aes_key, ctx->aes_iv, ciphertext, ciphertext_len,
                         &decrypted, &decrypted_len))
    {
        fprintf(stderr, "Decryption failed\n");
        free(ciphertext);
        return;
    }

    decrypted = realloc(decrypted, (size_t)decrypted_len + 1);
    decrypted[decrypted_len] = '\0';

    print_hex("AES-256 key: ", ctx->aes_key, sizeof(ctx->aes_key));
    print_hex("IV:          ", ctx->aes_iv, sizeof(ctx->aes_iv));
    printf("Plaintext:   %s\n", message);
    print_hex("Ciphertext:  ", ciphertext, ciphertext_len);
    printf("Decrypted:   %s\n", decrypted);

    free(ciphertext);
    free(decrypted);
}

void task_3(task_context *ctx)
{
    printf("\n\nTask 3:\n");

    print_hex("AES-256 key: ", ctx->aes_key, sizeof(ctx->aes_key));

    mpz_t cipher;
    mpz_init(cipher);
    rsa_encrypt_key(cipher, ctx->aes_key, ctx->rsa_key);

    gmp_printf("Encrypted AES key (RSA ciphertext): %Zx\n", cipher);

    unsigned char recovered_key[AES_KEY_SIZE];
    rsa_decrypt_key(recovered_key, cipher, ctx->rsa_key);
    print_hex("Decrypted AES-256 key: ", recovered_key, sizeof recovered_key);

    if (memcmp(ctx->aes_key, recovered_key, AES_KEY_SIZE) == 0)
        printf("AES key successfully recovered via RSA.\n");
    else
        printf("AES key mismatch.\n");

    mpz_clear(cipher);
}

void task_4(task_context *ctx)
{
    printf("\n\nTask 4:\n");
    printf("Encrypting image...\n");
    aes_encrypt_file("original.png", "encrypted.png", ctx->aes_key, ctx->aes_iv);
    printf("Image encrypted and saved as 'encrypted.png'\n");

    printf("Decrypting image...\n");
    aes_decrypt_file("encrypted.png", "decrypted.png", ctx->aes_key);
    printf("Decrypted image saved as 'decrypted.png'\n");
}

void task_5(task_context *ctx)
{
    printf("\n\nTask 5:\n");

    mpz_t cipher;
    mpz_init(cipher);
    rsa_encrypt_key(cipher, ctx->aes_key, ctx->rsa_key);

    unsigned char recovered_key[AES_KEY_SIZE];
    const int     N = 1000;
    double        t0 = now_sec();

    for (int i = 0; i < N; i++)
        rsa_decrypt_key(recovered_key, cipher, ctx->rsa_key);

    double t1 = now_sec();
    double t2 = now_sec();

    for (int i = 0; i < N; i++)
        rsa_decrypt_key_crt(recovered_key, cipher, ctx->rsa_key);

    double t3 = now_sec();

    double ms_std = (t1 - t0) * 1000.0 / N;
    double ms_crt = (t3 - t2) * 1000.0 / N;
    printf("\nStandard RSA decryption: %.3f ms/op\n", ms_std);
    printf("CRT RSA decryption:      %.3f ms/op\n", ms_crt);
    printf("Speedup (std / CRT):     %.2fx\n", ms_std / ms_crt);
}

int main(int argc, char **argv)
{
    task_context *ctx;

    ctx = malloc(sizeof(task_context));
    if (!ctx)
    {
        perror("malloc");
        exit(EXIT_FAILURE);
    }

    mpz_inits(ctx->rsa_key.d, ctx->rsa_key.e, ctx->rsa_key.n, NULL);
    bbs_init(&ctx->bbs, 1024);

    task_1(ctx);

    task_2(ctx);

    task_3(ctx);

    task_4(ctx);

    task_5(ctx);

    mpz_clears(ctx->rsa_key.d, ctx->rsa_key.e, ctx->rsa_key.n, NULL);
    bbs_clear(&ctx->bbs);
    free(ctx);

    return EXIT_SUCCESS;
}
