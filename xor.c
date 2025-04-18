#include <inttypes.h>

uint32_t xor(uint32_t c, uint32_t k){
    return c^k;
}

// is the above a good cipher. Does it have any weak keys?
// i.e for all k, c xor(c, k) != k