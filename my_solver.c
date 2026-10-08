#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "table.h"

enum{
    CUBIES = 7,
    MOVES = 9,
    TRACKED = 4,
    PDB_PERM = 840,     /* 7x6x5x4 */
    PDB_ORI = 81,       /* 3^4 */
    PDB_SIZE = PDB_ORI * PDB_PERM,
    UNSEEN = 0xF,
    MAX_DEPTH = 11, /* limited diameter in this metric */
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

static const uint8_t ids_a[TRACKED] = {0, 1, 2, 3};     /* Only looks at the positions and orientations of corner cubies 0 to 3. */
static const uint8_t ids_b[TRACKED] = {3, 4, 5, 6};     /* Only looks at the positions and orientations of corner cubies 3 to 6. */

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

static uint8_t path[MAX_DEPTH];                         /* Stores the moves along the current search path. */
static uint8_t solution_length;                         /* Stores the depth of the current solution. */


static state_t quarter_turn(state_t state, uint8_t face){
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move){
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}   


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

static int is_solved(const state_t *state){
    for(uint8_t i = 0; i < CUBIES; ++i){
        if(state->p[i] != i || state->o[i] != 0)
            return 0;
    }
    return 1;
}

/* ------------------------------------------------------------------ */
/* IDA*                                                                */
/* ------------------------------------------------------------------ */


/*
 * Each PDB lower-bounds the true distance (it solves a relaxed problem),
 * so their maximum is an admissible heuristic. We cannot add them: the
 * two patterns share cubie 3 and moves touch several cubies at once.
 */
static uint8_t heuristic(const state_t *state){
    uint8_t ha = pdb_get(pdb_a, pattern_encode(state, ids_a));
    uint8_t hb = pdb_get(pdb_b, pattern_encode(state, ids_b));
    return ha > hb ? ha : hb;
}


/* Returns 1 = solved, -1 = pruned, 0 = continue expanding */
static int visit(const state_t *state, uint8_t g, uint8_t threshold){
    if(g + heuristic(state) > threshold)                /* the node cannot reach a solution within the current threshold, so it is pruned. */
        return -1;              

    if(is_solved(state)){
        solution_length = g;
        return 1;
    }

    if(g >= threshold)                                  /* the search has reached the maximum depth allowed by the current threshold. */
        return -1;

    return 0;
}

static int search(state_t start, uint8_t threshold){
    state_t states[MAX_DEPTH + 1];     
    uint8_t next_move[MAX_DEPTH + 1];  
    uint8_t last_face[MAX_DEPTH + 1]; 
    uint8_t g = 0;
    int status;

    states[0] = start;
    last_face[0] = 3;

    status = visit(&states[0], 0, threshold);
    if(status == 1)
        return 1;
    if(status < 0)
        return 0;
    next_move[0] = 0;

    while(1){
        uint8_t move, face;

        if(next_move[g] >= MOVES){      
            if(g == 0)
                return 0;
            --g;
            continue;
        }

        move = next_move[g]++;
        face = (uint8_t) (move / 3U);
        if(face == last_face[g])       
            continue;

        path[g] = move;
        states[g + 1] = apply_move(states[g], move);
        last_face[g + 1] = face;

        status = visit(&states[g + 1], (uint8_t) (g + 1U), threshold);
        if(status == 1)
            return 1;
        if(status == 0){                
            ++g;
            next_move[g] = 0;
        }
    }
}

/*
 * Perform IDA* by repeatedly increasing the f-cost (sum of the path cost g and the heuristic estimate h.) threshold.
 * The initial threshold is the heuristic value of the start state.
 */

static int IDA_star(state_t start){
    for(uint8_t threshold = heuristic(&start); threshold <= MAX_DEPTH; ++threshold){
        if (search(start, threshold))
            return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ */


static int valid(const state_t *state){
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
}

static int parse_state(const char *input, state_t *state){
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}


int main(int argc, char **argv){
    state_t state;
    
    if(argc != 2 || !parse_state(argv[1], &state)){
        /* C99 5.1.2.2.1 lets argv[0] be null when argc is 0. */
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n", argc > 0 && argv[0] ? argv[0] : "solver");
        return 2;
    }

    if(!IDA_star(state)){
        fputs("no solution found\n", stderr);
        return 1;
    }

    for(uint8_t i = 0; i < solution_length; ++i)
        printf("%s%s", i ? " " : "", move_names[path[i]]);

    putchar('\n');

}