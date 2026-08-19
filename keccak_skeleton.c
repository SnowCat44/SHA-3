#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

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

static void rho(uint64_t *state) {
    int x, y;

    for (x = 0; x < 5; x++) {
        for (y = 0; y < 5; y++) {
            if (KeccakF_RhoOffsets[x][y] != 0) {
                state[x + 5 * y] = ROT(state[x + 5 * y], KeccakF_RhoOffsets[x][y]);
            }
        }
    }
}

static void pi(uint64_t *state) {
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

static void chi(uint64_t *state) {
    /* TODO */
}

static void iota(uint64_t *state, unsigned int round) {
    /* TODO */
}

static void KeccakF1600_StatePermute(uint64_t *state) {
    /* TODO: round = 0 .. NROUNDS-1 에 대해 theta/rho/pi/chi/iota 순으로 적용 */
}

static void keccak_absorb(uint64_t *s, uint32_t r, const uint8_t *m,
                          size_t mlen, uint8_t p) {
    size_t i;
    uint8_t t[200];

    for (i = 0; i < 25; i++) {
        s[i] = 0;
    }

    while (mlen >= r) {
        for (i = 0; i < r / 8; i++) {
            s[i] ^= load64(m + 8 * i);
        }
        KeccakF1600_StatePermute(s);
        m += r;
        mlen -= r;
    }

    for (i = 0; i < r; i++) {
        t[i] = 0;
    }
    for (i = 0; i < mlen; i++) {
        t[i] = m[i];
    }
    t[mlen] = p;
    t[r - 1] |= 0x80;

    for (i = 0; i < r / 8; i++) {
        s[i] ^= load64(t + 8 * i);
    }
}

static void keccak_squeezeblocks(uint8_t *h, size_t nblocks,
                                 uint64_t *s, uint32_t r) {
    KeccakF1600_StatePermute(s);

    while (nblocks > 0) {
        for (size_t i = 0; i < (r>>3); i++) {
            store64(h + 8 * i, s[i]);
        }
        KeccakF1600_StatePermute(s);
        h += r;
        nblocks--;
    }
}

void printvec(unsigned long long state[25])
{
    int i=3, j=3;
    for(int count =0 ; count < 5; count++){
        for(int count2 =0 ; count2 < 5; count2++){
            printf("%016llX,\t ",state[i*5+j]);
            j = (j+1)%5;
        }
        printf("\n");
        i = (i+1)%5;
    }
}

int main(void)
{
    uint64_t s[25];
    const uint32_t r_bytes = SHA3_RATE / 8;
    const uint8_t pad = 0x06;

    keccak_absorb(s, r_bytes, msg, sizeof(msg), pad);

    printvec(s);
    theta(s);
    printvec(s);

    printvec(s);
    rho(s);
    printvec(s);

    return 0;
}
