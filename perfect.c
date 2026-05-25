#include <stdio.h>

void init(void)
{
  // precompute a set of lookup tables to be used by rank.
}

uint64_t rank_rec(int n, int mult[], int sq[], int group_id, int r, int orbit,
    Bitboard occ)
{
  // n is the number of elements in mult[]
  //
  // mult[0], mult[1], ..., mult[n-1] are multiplicities >= 1
  //
  // sq[] is an array of mult[0] + ... + mult[n-1] squares on a chessboard (0-63)
  // The first mult[0] elements of sq[] correspond to one piece type
  // The next mult[1] elements of sq[] correspond to a second piece type, etc.
  //
  // group_id identifies one of the 10 subgroups of D8 (including D8)
  // - the placement of already placed pieces on the squares identified
  //   by the occ bitboard is symmetrical under this symmetry group.
  //
  // r is the number of remaining pieces in the "current group being placed"
  // as explained below. This number is not included in n or mult[].
  //
  // orbit is the number of the orbit under the symmetry group identified by
  // group_id starting from which the remaining pieces may be placed (if r > 0).
  //
  // occ is a bitboard of the squares that have already received a piece (not
  // included in n and mult[]).
  //
  // The value returned by rank is a value from 0 to N-1, where N is the
  // total number of unique placements for mult[] pieces up to D8 symmetry of
  // the chess board.
  //
  // The method used for calculating the rank is as follows:
  // - start with the symmetry group D8 and the set of empty orbits of the
  //   chess board under D8 (6 orbits of size 8, 4 orbits of size 4).
  // - Order the orbits, with the largest orbits ranked before the smaller
  //   orbits.
  // - Find the lowest-ranking orbit that receives one or more of the mult[0]
  //   pieces of the first group of pieces.
  // - Consider the possible canonical ways in which to place pieces in this
  //   lowest-ranking orbit and order these placements.
  // - Each of these placements corresponds to a number of ways in which the
  //   remaining pieces can be placed (a "completion number").
  //   This number is determined by a "state" which is defined by the
  //   following information:
  //   - the symmetry (sub)group H of remaining symmetries (after canonicalizing
  //     the pieces in the beforementioned lowest-ranking orbit). Note that
  //     we may have H = D8, but usually one, more or all symmetries will break.
  //   - the multiplicities of the types of empty orbits under H.
  //     - Note that H-orbits that received at least one piece will have
  //       necessarily received a piece on each of its squares.
  //     - Although in general not all orbits under an action of a group G
  //       having the same size will be the "same" as a G-set, in the case
  //       of the chessboard I have verified that all H-orbits of the same
  //       size are isomorphic as H-sets, for each of the 10 subgroups H of D8.
  //   - the multiplicities mult[] of the remaining groups of pieces.
  //   - the number of remaining pieces in the group of pieces currently
  //     being placed (possibly 0).
  //   - an indication of the first empty H-orbit that may receive further
  //     pieces from the remaining pieces in the group of pieces currently
  //     being placed (if >0).
  //     - For this to work, if H is smaller than D8 (or the previous group G
  //       of symmetries), then the smaller H-orbits must be ordered in a way
  //       that respects the order of the D8-orbits (or G-orbits). I believe
  //       this does not prevent us from ordering the H-orbits by descending
  //       size in the specific case of the chessboard and the D8 subgroups.
  // - to calculate the rank, we must sum the completion numbers for each
  //   of the possible canonical placements preceding the current placement
  //   (within the lowest-ranked orbit) and then recursively invoke the
  //   rank function for the remaining pieces (passing correct state, etc.)
  //   - potentially it could be useful to pass a bitboard with the already
  //     placed pieces, from which multiplicities of empty H-orbits can be
  //     arrived, but other approaches may work as well.
  // - Make a precomputed table to speed up the calculation as much as
  //   reasonably possible.
}

uint64_t rank(int n, int mult[], int sq[])
{
  return rank_rec(n, mult, sq, 0, 0, 0);
}

Bitboard unrank(int n, int mult[], int rk, int out[])
{
  // unrank() function corresponding to rank()
}

int main(int argc, char *argv[])
{
  init();

  // Test rank() and unrank() on some positions.
}
