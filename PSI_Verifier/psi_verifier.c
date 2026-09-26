#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "shared.h"
#include "omp.h"

#define RANDOMNESS_SIZE 1472

int mpc_AND_EQ_verify(
    uint32_t x[2],
    uint32_t y[2],
    uint32_t z[2],
    View ve,
    View ve1,
    unsigned char *randomness[2],
    int *randCount,
    int *countY
) {
    uint32_t r[2];

    r[0] = getRandom32(
        randomness[0],
        *randCount
    );

    r[1] = getRandom32(
        randomness[1],
        *randCount
    );

    *randCount += 4;

    uint32_t t =
        (x[0] & y[1]) ^
        (x[1] & y[0]) ^
        (x[0] & y[0]) ^
        r[0] ^
        r[1];

    if (ve.y[*countY] != t) {
        return 1;
    }

    z[0] = t;
    z[1] = ve1.y[*countY];

    (*countY)++;

    return 0;
}

int verify_equality_circuit(
    z proof
) {
    unsigned char *randomness[2];

    randomness[0] =
        malloc(RANDOMNESS_SIZE);

    randomness[1] =
        malloc(RANDOMNESS_SIZE);

    if (
        randomness[0] == NULL ||
        randomness[1] == NULL
    ) {
        free(randomness[0]);
        free(randomness[1]);
        return 1;
    }

    getAllRandomness(
        proof.ke,
        randomness[0]
    );

    getAllRandomness(
        proof.ke1,
        randomness[1]
    );

    int randCount = 0;
    int countY = 0;

    uint32_t eq[2] = {1, 0};

    uint32_t xbit[2];
    uint32_t ybit[2];

    uint32_t diff[2];
    uint32_t same[2];

    uint32_t temp[2];

    for (int bit = 0; bit < 8; bit++) {
        xbit[0] =
            (proof.ve.x[0] >> bit) & 1;

        xbit[1] =
            (proof.ve1.x[0] >> bit) & 1;

        ybit[0] =
            (proof.ve.x[1] >> bit) & 1;

        ybit[1] =
            (proof.ve1.x[1] >> bit) & 1;

        mpc_XOR2(
            xbit,
            ybit,
            diff
        );

        same[0] = diff[0];
        same[1] = diff[1];

        same[0] ^= 1;

        if (
            mpc_AND_EQ_verify(
                eq,
                same,
                temp,
                proof.ve,
                proof.ve1,
                randomness,
                &randCount,
                &countY
            ) != 0
        ) {
            free(randomness[0]);
            free(randomness[1]);
            return 1;
        }

        eq[0] = temp[0] & 1;
        eq[1] = temp[1] & 1;
    }

    uint32_t expected0 =
        proof.ve.y[ySize - 5];

    uint32_t expected1 =
        proof.ve1.y[ySize - 5];

    if (eq[0] != expected0) {
        free(randomness[0]);
        free(randomness[1]);
        return 1;
    }

    if (eq[1] != expected1) {
        free(randomness[0]);
        free(randomness[1]);
        return 1;
    }

    free(randomness[0]);
    free(randomness[1]);

    return 0;
}

int verify_equality(
    a proofA,
    int challenge,
    z proof
) {
    unsigned char hash[SHA256_DIGEST_LENGTH];

    H(
        proof.ke,
        proof.ve,
        proof.re,
        hash
    );

    if (
        memcmp(
            proofA.h[challenge],
            hash,
            32
        ) != 0
    ) {
        return 1;
    }

    H(
        proof.ke1,
        proof.ve1,
        proof.re1,
        hash
    );

    if (
        memcmp(
            proofA.h[(challenge + 1) % 3],
            hash,
            32
        ) != 0
    ) {
        return 1;
    }

    uint32_t result[8];

    output(
        proof.ve,
        result
    );

    if (
        memcmp(
            proofA.yp[challenge],
            result,
            20
        ) != 0
    ) {
        return 1;
    }

    output(
        proof.ve1,
        result
    );

    if (
        memcmp(
            proofA.yp[(challenge + 1) % 3],
            result,
            20
        ) != 0
    ) {
        return 1;
    }

    if (
        verify_equality_circuit(
            proof
        ) != 0
    ) {
        return 1;
    }

    return 0;
}

int main(void) {
    setbuf(stdout, NULL);

    init_EVP();
    openmp_thread_setup();

    FILE *file =
        fopen(
            "out_equality.bin",
            "rb"
        );

    if (file == NULL) {
        printf(
            "Unable to open out_equality.bin\n"
        );

        openmp_thread_cleanup();
        cleanup_EVP();

        return 1;
    }

    a proofA[NUM_ROUNDS];

    z proofs[NUM_ROUNDS];

    size_t readA =
        fread(
            proofA,
            sizeof(a),
            NUM_ROUNDS,
            file
        );

    if (readA != NUM_ROUNDS) {
        printf(
            "Error reading commitments.\n"
        );

        fclose(file);
        openmp_thread_cleanup();
        cleanup_EVP();

        return 1;
    }

    size_t readZ =
        fread(
            proofs,
            sizeof(z),
            NUM_ROUNDS,
            file
        );

    if (readZ != NUM_ROUNDS) {
        printf(
            "Error reading data.\n"
        );

        fclose(file);
        openmp_thread_cleanup();
        cleanup_EVP();

        return 1;
    }

    fclose(file);

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

    uint32_t reconstructedResult =
        finalHash[0];

    printf(
        "Public circuit result: %u\n\n",
        reconstructedResult
    );

    if (reconstructedResult != 1) {
        printf(
            "RESULT: Invalid\n"
        );

        printf(
            "The proof does not prove x == y.\n"
        );

        openmp_thread_cleanup();
        cleanup_EVP();

        return 1;
    }

    printf(
        "Checking %d rounds...\n\n",
        NUM_ROUNDS
    );

    for (int round = 0;
         round < NUM_ROUNDS;
         round++) {

        if (
            verify_equality(
                proofA[round],
                challenges[round],
                proofs[round]
            ) != 0
        ) {
            printf(
                "Round %d: Fail\n",
                round + 1
            );

            printf(
                "\nRESULT: Invalid\n"
            );

            openmp_thread_cleanup();
            cleanup_EVP();

            return 1;
        }

        printf(
            "Round %d: OK\n",
            round + 1
        );
    }


    printf(
        "RESULT: Valid\n"
    );

    printf(
        "The proof establishes x == y.\n"
    );

    openmp_thread_cleanup();
    cleanup_EVP();

    return 0;
}
