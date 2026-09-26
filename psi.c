#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "shared.h"
#include "omp.h"

#define INPUT_BYTES 2
#define RANDOMNESS_SIZE 1472

void mpc_XOR_EQ(uint32_t x[3], uint32_t y[3], uint32_t z[3]) {
    z[0] = x[0] ^ y[0];
    z[1] = x[1] ^ y[1];
    z[2] = x[2] ^ y[2];
}

void mpc_AND_EQ(
    uint32_t x[3],
    uint32_t y[3],
    uint32_t z[3],
    unsigned char *randomness[3],
    int *randCount,
    View views[3],
    int *countY
) {
    uint32_t r[3];

    r[0] = getRandom32(randomness[0], *randCount);
    r[1] = getRandom32(randomness[1], *randCount);
    r[2] = getRandom32(randomness[2], *randCount);

    *randCount += 4;

    z[0] =
        (x[0] & y[1]) ^
        (x[1] & y[0]) ^
        (x[0] & y[0]) ^
        r[0] ^
        r[1];

    z[1] =
        (x[1] & y[2]) ^
        (x[2] & y[1]) ^
        (x[1] & y[1]) ^
        r[1] ^
        r[2];

    z[2] =
        (x[2] & y[0]) ^
        (x[0] & y[2]) ^
        (x[2] & y[2]) ^
        r[2] ^
        r[0];

    views[0].y[*countY] = z[0];
    views[1].y[*countY] = z[1];
    views[2].y[*countY] = z[2];

    (*countY)++;
}

void mpc_EQUALITY(
    unsigned char shares[3][INPUT_BYTES],
    unsigned char *randomness[3],
    View views[3],
    uint32_t result[3]
) {
    int randCount = 0;
    int countY = 0;

    uint32_t eq[3] = {1, 0, 0};

    uint32_t xbit[3];
    uint32_t ybit[3];
    uint32_t diff[3];
    uint32_t same[3];
    uint32_t temp[3];

    for (int bit = 0; bit < 8; bit++) {
        xbit[0] = (shares[0][0] >> bit) & 1;
        xbit[1] = (shares[1][0] >> bit) & 1;
        xbit[2] = (shares[2][0] >> bit) & 1;

        ybit[0] = (shares[0][1] >> bit) & 1;
        ybit[1] = (shares[1][1] >> bit) & 1;
        ybit[2] = (shares[2][1] >> bit) & 1;

        mpc_XOR_EQ(xbit, ybit, diff);

        same[0] = diff[0];
        same[1] = diff[1];
        same[2] = diff[2];

        same[0] ^= 1;

        mpc_AND_EQ(
            eq,
            same,
            temp,
            randomness,
            &randCount,
            views,
            &countY
        );

        eq[0] = temp[0] & 1;
        eq[1] = temp[1] & 1;
        eq[2] = temp[2] & 1;
    }

    result[0] = eq[0];
    result[1] = eq[1];
    result[2] = eq[2];

    views[0].y[ySize - 5] = result[0];
    views[1].y[ySize - 5] = result[1];
    views[2].y[ySize - 5] = result[2];

    for (int i = 1; i < 5; i++) {
        views[0].y[ySize - 5 + i] = 0;
        views[1].y[ySize - 5 + i] = 0;
        views[2].y[ySize - 5 + i] = 0;
    }
}

void commit_hashes(
    unsigned char keys[3][16],
    unsigned char rs[3][4],
    View views[3],
    a *proofA
) {
    H(
        keys[0],
        views[0],
        rs[0],
        proofA->h[0]
    );

    H(
        keys[1],
        views[1],
        rs[1],
        proofA->h[1]
    );

    H(
        keys[2],
        views[2],
        rs[2],
        proofA->h[2]
    );
}

z prove_equality(
    int e,
    unsigned char keys[3][16],
    unsigned char rs[3][4],
    View views[3]
) {
    z proof;

    memcpy(proof.ke, keys[e], 16);
    memcpy(proof.ke1, keys[(e + 1) % 3], 16);

    proof.ve = views[e];
    proof.ve1 = views[(e + 1) % 3];

    memcpy(proof.re, rs[e], 4);
    memcpy(proof.re1, rs[(e + 1) % 3], 4);

    return proof;
}

int main(void) {
    setbuf(stdout, NULL);

    init_EVP();
    openmp_thread_setup();

    unsigned char x = 2;
    unsigned char y = 3;

    printf("x = %u\n", x);
    printf("y = %u\n\n", y);

    unsigned char input[INPUT_BYTES];

    input[0] = x;
    input[1] = y;

    unsigned char keys[NUM_ROUNDS][3][16];
    unsigned char rs[NUM_ROUNDS][3][4];

    View views[NUM_ROUNDS][3];
    a proofA[NUM_ROUNDS];

    unsigned char shares[NUM_ROUNDS][3][INPUT_BYTES];

    if (RAND_bytes(
            (unsigned char *)keys,
            sizeof(keys)
        ) != 1) {
        printf("RAND_bytes failed.\n");
        return 1;
    }

    if (RAND_bytes(
            (unsigned char *)rs,
            sizeof(rs)
        ) != 1) {
        printf("RAND_bytes failed.\n");
        return 1;
    }

    if (RAND_bytes(
            (unsigned char *)shares,
            sizeof(shares)
        ) != 1) {
        printf("RAND_bytes failed.\n");
        return 1;
    }

    for (int round = 0; round < NUM_ROUNDS; round++) {
        for (int j = 0; j < INPUT_BYTES; j++) {
            shares[round][2][j] =
                input[j] ^
                shares[round][0][j] ^
                shares[round][1][j];
        }
    }

    unsigned char *randomness[3];

    for (int round = 0; round < NUM_ROUNDS; round++) {
        for (int party = 0; party < 3; party++) {
            randomness[party] =
                malloc(RANDOMNESS_SIZE);

            if (randomness[party] == NULL) {
                printf("Memory allocation failed.\n");
                return 1;
            }

            getAllRandomness(
                keys[round][party],
                randomness[party]
            );
        }

        memset(
            &views[round],
            0,
            sizeof(View) * 3
        );

        uint32_t result[3];

        mpc_EQUALITY(
            shares[round],
            randomness,
            views[round],
            result
        );

        proofA[round].yp[0][0] = result[0];
        proofA[round].yp[1][0] = result[1];
        proofA[round].yp[2][0] = result[2];

        for (int party = 0; party < 3; party++) {
            for (int j = 1; j < 8; j++) {
                proofA[round].yp[party][j] = 0;
            }
        }

        for (int party = 0; party < 3; party++) {
            H(
                keys[round][party],
                views[round][party],
                rs[round][party],
                proofA[round].h[party]
            );
        }

        for (int party = 0; party < 3; party++) {
            free(randomness[party]);
        }
    }

    uint32_t finalHash[8];

    for (int j = 0; j < 8; j++) {
        finalHash[j] =
            proofA[0].yp[0][j] ^
            proofA[0].yp[1][j] ^
            proofA[0].yp[2][j];
    }

    int challenges[NUM_ROUNDS];

    H3(
        finalHash,
        proofA,
        NUM_ROUNDS,
        challenges
    );

    z proofs[NUM_ROUNDS];

    for (int round = 0; round < NUM_ROUNDS; round++) {
        proofs[round] =
            prove_equality(
                challenges[round],
                keys[round],
                rs[round],
                views[round]
            );
    }

    FILE *file = fopen(
        "out_equality.bin",
        "wb"
    );

    if (file == NULL) {
        printf("Unable to create out_equality.bin\n");
        return 1;
    }

    fwrite(
        proofA,
        sizeof(a),
        NUM_ROUNDS,
        file
    );

    fwrite(
        proofs,
        sizeof(z),
        NUM_ROUNDS,
        file
    );

    fclose(file);

    uint32_t reconstructed =
        proofA[0].yp[0][0] ^
        proofA[0].yp[1][0] ^
        proofA[0].yp[2][0];

    printf("\nCircuit result: %u\n", reconstructed);

    if (reconstructed == 1) {
        printf("Equality x == y: TRUE\n");
    } else {
        printf("Equality x == y: FALSE\n");
    }

    printf("\nProof generated successfully.\n");
    printf("Output: out_equality.bin\n");

    openmp_thread_cleanup();
    cleanup_EVP();

    return 0;
}
