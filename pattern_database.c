#include <stdio.h>
#include <stdint.h>
#include <string.h>

enum{
    CUBIES = 7,
    MOVES = 9,
    TRACKED = 4,
    PDB_PERM = 840,     /* 7x6x5x4 */
    PDB_ORI = 81,       /* 3^4 */
    PDB_SIZE = PDB_ORI * PDB_PERM,
    PDB_BYTES = PDB_SIZE / 2,
    UNSEEN = 0xF
};

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};

/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

static const uint8_t ids_a[TRACKED] = {0, 1, 2, 3};     //Only looks at the positions and orientations of corner cubies 0 to 3.
static const uint8_t ids_b[TRACKED] = {3, 4, 5, 6};     //Only looks at the positions and orientations of corner cubies 3 to 6.

static uint8_t pdb_a[PDB_BYTES];
static uint8_t pdb_b[PDB_BYTES];

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;


/* Read a 4-bit entry from the packed pattern database. */ 
static uint8_t pdb_get(const uint8_t *pdb, uint32_t index){
    return (uint8_t) ((pdb[index >> 1] >> ((index & 1U) * 4U)) & 0xFU);
}

/* Write a 4-bit entry to the packed pattern database. */
static void pdb_set(uint8_t *pdb, uint32_t index, uint8_t value){
    uint32_t shift = (index & 1U) * 4U;
    pdb[index >> 1] = (uint8_t) ((pdb[index >> 1] & ~(0xFU << shift)) | (value << shift));
}

/* Pack the tracked cubies' permutation and orientation into a single index */
static uint32_t pattern_pack(const uint8_t perm[TRACKED], const uint8_t ori[TRACKED]){
    static const uint8_t radix[TRACKED] = {7, 6, 5, 4};
    uint32_t p = 0, o = 0;
    for (uint8_t k = 0; k < TRACKED; ++k){
        uint8_t rank = perm[k];
        for (uint8_t j = 0; j < k; ++j){
            if (perm[j] < perm[k]) 
                --rank;
        }
        p = p * radix[k] + rank;
        o = o * 3U + ori[k];
    }
    return p * PDB_ORI + o;
}

/* Unpack a pattern database index back into permutation and orientation. (reverses the encoding performed by pattern_pack())*/
static void pattern_unpack(uint32_t code, uint8_t perm[TRACKED], uint8_t ori[TRACKED]){
    uint32_t pc = code / PDB_ORI, oc = code % PDB_ORI;
    uint8_t rank[TRACKED];
    uint8_t used[CUBIES] = {0};

    rank[3] = (uint8_t) (pc % 4U);
    pc /= 4U;
    rank[2] = (uint8_t) (pc % 5U);
    pc /= 5U;
    rank[1] = (uint8_t) (pc % 6U);
    pc /= 6U;
    rank[0] = (uint8_t) pc;
    for(uint8_t k = TRACKED; k-- > 0;){
        ori[k] = (uint8_t) (oc % 3U);
        oc /= 3U;
    }

    for(uint8_t k = 0; k < TRACKED; ++k){
        uint8_t skip = rank[k], x = 0;
        for (;; ++x)
            if (!used[x] && skip-- == 0)
                break;
        used[x] = 1;
        perm[k] = x;
    }
}

/*Extract the tracked cubies from the full cube state and encode their permutation and orientation into a pattern index.*/
static uint32_t pattern_encode(const state_t *state, const uint8_t ids[TRACKED]){
    uint8_t perm[TRACKED] = {0}, ori[TRACKED] = {0};
    for (uint8_t i = 0; i < CUBIES; ++i)
        for (uint8_t k = 0; k < TRACKED; ++k)
            if (state->p[i] == ids[k]) {
                perm[k] = i;
                ori[k] = state->o[i];
            }
    return pattern_pack(perm, ori);
}

/* Apply one move directly on a pattern code (no full state needed). */
static uint32_t pattern_move(uint32_t code, uint8_t move){
    uint8_t perm[TRACKED], ori[TRACKED];
    uint8_t face = (uint8_t) (move / 3U);
    uint8_t turns = (uint8_t) (move % 3U + 1U);

    pattern_unpack(code, perm, ori);
    while (turns--)
        for (uint8_t k = 0; k < TRACKED; ++k) {
            uint8_t dest = 0;
            while (source[face][dest] != perm[k])
                ++dest;
            perm[k] = dest;
            ori[k] = (uint8_t) ((ori[k] + twist[face][dest]) % 3U);
        }
    return pattern_pack(perm, ori);
}

static uint32_t build_pdb(uint8_t *pdb, const uint8_t ids[TRACKED], uint8_t *max_distance){
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    uint32_t reached = 1;
    uint8_t depth = 0;

    memset(pdb, 0xFF, PDB_BYTES);
    pdb_set(pdb, pattern_encode(&solved, ids), 0);
    while(1){
        uint32_t added = 0;
        for (uint32_t code = 0; code < PDB_SIZE; ++code){
            if (pdb_get(pdb, code) != depth)
                continue;
            for (uint8_t move = 0; move < MOVES; ++move){
                uint32_t next = pattern_move(code, move);
                if (pdb_get(pdb, next) == UNSEEN) {
                    pdb_set(pdb, next, (uint8_t) (depth + 1U));
                    ++added;
                }
            }
        }
        if(!added)
            break;
        reached += added;
        ++depth;
    }

    *max_distance = depth;
    return reached;
}

static void emit(FILE *f, const char *name, const uint8_t *t){
    fprintf(f, "static const uint8_t %s[PDB_BYTES] = {", name);
    for (uint32_t i = 0; i < PDB_BYTES; ++i)
        fprintf(f, "%s%u,", i % 24 ? "" : "\n    ", t[i]);
    fputs("\n};\n", f);
}

int main(){
    state_t state;
    uint8_t max_dist_a, max_dist_b;
    uint32_t reach_a = build_pdb(pdb_a, ids_a, &max_dist_a);
    uint32_t reach_b = build_pdb(pdb_b, ids_b, &max_dist_b);

    FILE *f = fopen("table.h", "a");
    if (!f) return 1;
    emit(f, "pdb_a", pdb_a);
    emit(f, "pdb_b", pdb_b);
    return fclose(f) != 0;

}