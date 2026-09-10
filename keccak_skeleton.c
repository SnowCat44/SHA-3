#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define ROT(x, n) (((x) << (n)) | ((x) >> (64 - (n))))

#define SHA3_RATE     1152   /* r, bits (SHA3-224 파라미터) */
#define SHA3_CAPACITY 448    /* c, bits (r + c = 1600) */

static const uint8_t msg[] = {
    0x01, 0xc7, 0x42, 0xdc, 0x9a, 0xb0, 0xb0, 0x5d,
    0xf9, 0x25, 0xd4, 0xa3, 0x51, 0xe3, 0x8b, 0xea,
    0x7c, 0xa7, 0xad, 0x78, 0x35, 0x94, 0xe2, 0x24,
    0x87, 0xd5, 0xb8, 0x19, 0x85, 0x83, 0xf3
};
static const size_t msglen = 248 / 8;

unsigned long long test[25] = {
    0x5DB0B09ADC42C701, 0xEA8BE351A3D425F9, 0x24E2943578ADA77C, 0x06F3838519B8D587, 0x00,
    0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x8000000000000000,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00
};

static uint64_t load64(const uint8_t *x)
{
    uint64_t r = 0;
        for (size_t i = 0; i < 8; ++i) {
            r |= (uint64_t)x[i] << 8 * i;
        }
        return r;
}

static void store64(uint8_t *x, uint64_t u)
{
    size_t i;
    for (i = 0; i < 8; ++i) {
        x[i] = (uint8_t)(u >> 8 * i);
    }
}

/* Keccak round constants (iota 단계에서 사용) */
static const uint64_t KeccakF_RoundConstants[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL,
    0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL,
    0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL,
    0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL,
    0x0000000080000001ULL, 0x8000000080008008ULL
};

static const unsigned int KeccakF_RhoOffsets[5][5] = {
    {  0, 36,  3, 41, 18 },
    {  1, 44, 10, 45,  2 },
    { 62,  6, 43, 15, 61 },
    { 28, 55, 25, 21, 56 },
    { 27, 20, 39,  8, 14 }
};

static void theta(uint64_t *state)
{
    uint64_t C[5], D[5];
    int x, y;

    for (x = 0; x < 5; x++) {
        C[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    }

    for (x = 0; x < 5; x++) {
        D[x] = C[(x + 4) % 5] ^ ROT(C[(x + 1) % 5], 1);
        for (y = 0; y < 5; y++) {
            state[x + 5 * y] ^= D[x];
        }
    }
}

static void rho(uint64_t *state)
{
    int x, y;

    for (x = 0; x < 5; x++) {
        for (y = 0; y < 5; y++) {
            if (KeccakF_RhoOffsets[x][y] != 0) {
                state[x + 5 * y] = ROT(state[x + 5 * y], KeccakF_RhoOffsets[x][y]);
            }
        }
    }
}

static void pi(uint64_t *state)
{
    uint64_t tmp[25];
    int x, y, X, Y;

    for (x = 0; x < 5; x++) {
        for (y = 0; y < 5; y++) {
            tmp[x + 5 * y] = state[x + 5 * y];
        }
    }

    for (x = 0; x < 5; x++) {
        for (y = 0; y < 5; y++) {
            X = y;
            Y = (2 * x + 3 * y) % 5;
            state[X + 5 * Y] = tmp[x + 5 * y];
        }
    }
}

static void chi(uint64_t *state)
{
    uint64_t tmp[25];
    int x, y;

    for (x = 0; x < 5; x++) {
        for (y = 0; y < 5; y++) {
            tmp[x + 5 * y] = state[x + 5 * y];
        }
    }

    for (x = 0; x < 5; x++) {
        for (y = 0; y < 5; y++) {
            state[x + 5 * y] = tmp[x + 5 * y] ^ ((~tmp[(x + 1) % 5 + 5 * y]) & tmp[(x + 2) % 5 + 5 * y]);
        }
    }
}

static void iota(uint64_t *state, unsigned int round)
{
    state[0] ^= KeccakF_RoundConstants[round];
}

static void KeccakF1600_StatePermute(uint64_t *state)
{
    for (unsigned int round = 0; round < 24; round++) {
        theta(state);
        rho(state);
        pi(state);
        chi(state);
        iota(state, round);
    }
}

/*PQClean code*/
static void keccak_inc_init(uint64_t *s_inc) {
    size_t i;

    for (i = 0; i < 25; ++i) {
        s_inc[i] = 0;
    }
    s_inc[25] = 0;
}

static void keccak_inc_absorb(uint64_t *s_inc, uint32_t r, const uint8_t *m,
                              size_t mlen) {
    size_t i;

    /* Recall that s_inc[25] is the non-absorbed bytes xored into the state */
    while (mlen + s_inc[25] >= r) { // 이 부분에서 범위가 넘어가는지 계속 검사
        for (i = 0; i < r - (uint32_t)s_inc[25]; i++) {
            /* Take the i'th byte from message
               xor with the s_inc[25] + i'th byte of the state; little-endian */
            s_inc[(s_inc[25] + i) >> 3] ^= (uint64_t)m[i] << (8 * ((s_inc[25] + i) & 0x07));
        }
        mlen -= (size_t)(r - s_inc[25]);
        m += r - s_inc[25];
        s_inc[25] = 0;

        KeccakF1600_StatePermute(s_inc);
    }

    for (i = 0; i < mlen; i++) { // r 비트가 됬을 때, permutation을 수행
        s_inc[(s_inc[25] + i) >> 3] ^= (uint64_t)m[i] << (8 * ((s_inc[25] + i) & 0x07));
    }
    s_inc[25] += mlen;
}

static void keccak_inc_finalize(uint64_t *s_inc, uint32_t r, uint8_t p) {
    /* After keccak_inc_absorb, we are guaranteed that s_inc[25] < r,
       so we can always use one more byte for p in the current state. */
    s_inc[s_inc[25] >> 3] ^= (uint64_t)p << (8 * (s_inc[25] & 0x07));
    s_inc[(r - 1) >> 3] ^= (uint64_t)128 << (8 * ((r - 1) & 0x07));
    s_inc[25] = 0;
}

static void keccak_inc_squeeze(uint8_t *h, size_t outlen,
                               uint64_t *s_inc, uint32_t r) {
    size_t i;

    /* First consume any bytes we still have sitting around */
    for (i = 0; i < outlen && i < s_inc[25]; i++) {
        /* There are s_inc[25] bytes left, so r - s_inc[25] is the first
           available byte. We consume from there, i.e., up to r. */
        h[i] = (uint8_t)(s_inc[(r - s_inc[25] + i) >> 3] >> (8 * ((r - s_inc[25] + i) & 0x07)));
    }
    h += i;
    outlen -= i;
    s_inc[25] -= i;

    /* Then squeeze the remaining necessary blocks */
    while (outlen > 0) {
        KeccakF1600_StatePermute(s_inc);

        for (i = 0; i < outlen && i < r; i++) {
            h[i] = (uint8_t)(s_inc[i >> 3] >> (8 * (i & 0x07)));
        }
        h += i;
        outlen -= i;
        s_inc[25] = r - i;
    }
}

#define SHAKE128_RATE 168   /* r = 1344 bit / 8 (SHAKE128 파라미터) */

typedef struct {
    uint64_t ctx[26];
} shake128incctx;

void shake128_inc_init(shake128incctx *state) {
    keccak_inc_init(state->ctx);
}

void shake128_inc_absorb(shake128incctx *state, const uint8_t *input, size_t inlen) {
    keccak_inc_absorb(state->ctx, SHAKE128_RATE, input, inlen);
}

void shake128_inc_finalize(shake128incctx *state) {
    keccak_inc_finalize(state->ctx, SHAKE128_RATE, 0x1F);
}

void shake128_inc_squeeze(uint8_t *output, size_t outlen, shake128incctx *state) {
    keccak_inc_squeeze(output, outlen, state->ctx, SHAKE128_RATE);
}
/* End of PQClean code */

void printvec(unsigned long long state[25])
{
    int i=2, j=3;
    for(int count = 0 ; count < 5; count++){
        for(int count2 = 0 ; count2 < 5; count2++){
            printf("%016llX,\t ",state[i * 5 + j]);
            j = (j + 1) % 5;
        }
        printf("\n");
        i = (i + 4) % 5;
    }
}

int main(void)
{
    unsigned char buf[2696] = "a6fe00064257aa318b621c5eb311d32bb8004c2fa1a969d205d71762cc5d2e633907992629d1b69d9557ff6d5e8deb454ab00f6e497c89a4fea09e257a6fa2074bd818ceb5981b3e3faefd6e720f2d1edd9c5e4a5c51e5009abf636ed5bca53fe159c8287014a1bd904f5c8a7501625f79ac81eb618f478ce21cae6664acffb30572f059e1ad0fc2912264e8f1ca52af26c8bf78e09d75f3dd9fc734afa8770abe0bd78c90cc2ff448105fb16dd2c5b7edd8611a62e537db9331f5023e16d6ec150cc6e706d7c7fcbfff930c7281831fd5c4aff86ece57ed0db882f59a5fe403105d0592ca38a081fed84922873f538ee774f13b8cc09bd0521db4374aec69f4bae6dcb66455822c0b84c91a3474ffac2ad06f0a4423cd2c6a49d4f0d6242d6a1890937b5d9835a5f0ea5b1d01884d22a6c1718e1f60b3ab5e232947c76ef70b344171083c688093b5f1475377e3069863";
    unsigned char fine[128] = "";
    unsigned char output[128] = "3109d9472ca436e805c6b3db2251a9bc";

    shake128incctx st;

    shake128_inc_init(&st);
    shake128_inc_absorb(&st, buf, sizeof(buf));
    shake128_inc_finalize(&st);
    shake128_inc_squeeze(fine, sizeof(fine), &st);
    
    printf("SHAKE128 output (%zu bytes):\n", sizeof(output));
    for (size_t i = 0; i < sizeof(output); i++) {
        printf("%02x", fine[i]);
    }
    printf("\n");

    printf("Expected output: ");
    for (size_t i = 0; i < sizeof(output); i++) {
        printf("%02x", output[i]);
    }
    printf("\n");

    return 0;
}