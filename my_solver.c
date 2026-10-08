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

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;



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

int main(){

}