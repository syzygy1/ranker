#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t Bitboard;

#define BOARD_SIZE 64
#define BOARD_SIDE 8
#define D8_SIZE 8
#define FULL_D8 0xff
#define MAX_GROUPS 16
#define MAX_ORBITS 64
#define MAX_SUBSETS 256
#define SUBGROUP_COUNT 10
#define MAX_PIECES 8

typedef struct {
  Bitboard bb;
  int size;
  int min_sq;
  int cache_idx;
} Orbit;

typedef struct {
  Orbit orbit[MAX_ORBITS];
  int n;
} OrbitList;

typedef struct {
  Bitboard subset[MAX_SUBSETS];
  unsigned char stabilizer[MAX_SUBSETS];
  int n;
} SubsetList;

typedef struct {
  unsigned char group_mask;
  uint32_t rem_sig;
  unsigned char empty_by_size[BOARD_SIDE + 1];
  unsigned char allow_by_size[BOARD_SIDE + 1];
  uint64_t count;
} CountEntry;

typedef struct {
  int n;
  int mult[MAX_GROUPS];
  int total;
} Context;

static int map[D8_SIZE][BOARD_SIZE];
static const unsigned char subgroup_mask[SUBGROUP_COUNT] = {
  0x01, // identity
  0x05, // 180-degree rotations
  0x0f, // rotations
  0x11, // vertical reflection
  0x21, // horizontal reflection
  0x41, // main-diagonal reflection
  0x81, // anti-diagonal reflection
  0x35, // 180-degree rotation plus vertical/horizontal reflections
  0xc5, // 180-degree rotation plus diagonal reflections
  0xff  // full D8
};
static OrbitList subgroup_orbits[SUBGROUP_COUNT];
static SubsetList subset_cache[SUBGROUP_COUNT][MAX_ORBITS][BOARD_SIDE + 1];
static unsigned char orbit_idx_by_size[SUBGROUP_COUNT][BOARD_SIDE + 1];
static unsigned char decomp_by_size[SUBGROUP_COUNT][SUBGROUP_COUNT]
    [BOARD_SIDE + 1][BOARD_SIDE + 1];
static CountEntry *count_table;
static size_t count_table_len;
static size_t count_table_cap;
static int prebuilding_counts;
static int initialized;

static int bitcount(Bitboard b)
{
  int n = 0;

  while (b) {
    b &= b - 1;
    n++;
  }
  return n;
}

static int first_square(Bitboard b)
{
  for (int sq = 0; sq < BOARD_SIZE; sq++) {
    if (b & ((Bitboard)1 << sq)) {
      return sq;
    }
  }
  return -1;
}

static int take_square(Bitboard *b)
{
  int sq = first_square(*b);

  if (sq < 0) {
    abort();
  }
  *b &= ~((Bitboard)1 << sq);
  return sq;
}

static int transform_square_raw(int sq, int t)
{
  int r = sq / BOARD_SIDE;
  int c = sq % BOARD_SIDE;
  int nr = r;
  int nc = c;

  switch (t) {
  case 0: nr = r; nc = c; break;
  case 1: nr = c; nc = BOARD_SIDE - 1 - r; break;
  case 2: nr = BOARD_SIDE - 1 - r; nc = BOARD_SIDE - 1 - c; break;
  case 3: nr = BOARD_SIDE - 1 - c; nc = r; break;
  case 4: nr = r; nc = BOARD_SIDE - 1 - c; break;
  case 5: nr = BOARD_SIDE - 1 - r; nc = c; break;
  case 6: nr = c; nc = r; break;
  case 7: nr = BOARD_SIDE - 1 - c; nc = BOARD_SIDE - 1 - r; break;
  default: abort();
  }
  return nr * BOARD_SIDE + nc;
}

static Bitboard transform_bb(Bitboard b, int t)
{
  Bitboard out = 0;

  while (b) {
    int sq = take_square(&b);
    out |= (Bitboard)1 << map[t][sq];
  }
  return out;
}

static int orbit_cmp(const void *a, const void *b)
{
  const Orbit *oa = (const Orbit *)a;
  const Orbit *ob = (const Orbit *)b;

  if (oa->size != ob->size) {
    return ob->size - oa->size;
  }
  return oa->min_sq - ob->min_sq;
}

static int subgroup_index(unsigned char group_mask)
{
  for (int i = 0; i < SUBGROUP_COUNT; i++) {
    if (subgroup_mask[i] == group_mask) {
      return i;
    }
  }
  fprintf(stderr, "internal error: unknown D8 subgroup mask 0x%02x\n",
      group_mask);
  exit(1);
}

static Bitboard canonical_bb(Bitboard bb, unsigned char group_mask);
static void build_completion_tables(void);

static OrbitList build_empty_orbits(unsigned char group_mask)
{
  OrbitList list;
  Bitboard unseen = ~(Bitboard)0;

  memset(&list, 0, sizeof(list));
  while (unseen) {
    Bitboard orbit = 0;
    int seed = take_square(&unseen);

    for (int t = 0; t < D8_SIZE; t++) {
      if (group_mask & (1u << t)) {
        orbit |= (Bitboard)1 << map[t][seed];
      }
    }
    unseen &= ~orbit;
    list.orbit[list.n].bb = orbit;
    list.orbit[list.n].size = bitcount(orbit);
    list.orbit[list.n].min_sq = first_square(orbit);
    list.n++;
  }
  qsort(list.orbit, (size_t)list.n, sizeof(list.orbit[0]), orbit_cmp);
  for (int i = 0; i < list.n; i++) {
    list.orbit[i].cache_idx = i;
  }
  return list;
}

static void count_suborbits(Bitboard set, int subgroup, unsigned char out[])
{
  memset(out, 0, BOARD_SIDE + 1);
  for (int i = 0; i < subgroup_orbits[subgroup].n; i++) {
    const Orbit *orbit = &subgroup_orbits[subgroup].orbit[i];

    if ((orbit->bb & set) == orbit->bb) {
      out[orbit->size]++;
    } else if (orbit->bb & set) {
      fprintf(stderr, "internal error: set splits a subgroup orbit\n");
      exit(1);
    }
  }
}

static void build_decomposition_tables(void)
{
  for (int h = 0; h < SUBGROUP_COUNT; h++) {
    memset(orbit_idx_by_size[h], 0xff, sizeof(orbit_idx_by_size[h]));
    for (int i = 0; i < subgroup_orbits[h].n; i++) {
      int size = subgroup_orbits[h].orbit[i].size;

      if (orbit_idx_by_size[h][size] == 0xff) {
        orbit_idx_by_size[h][size] = (unsigned char)i;
      }
    }
  }

  memset(decomp_by_size, 0, sizeof(decomp_by_size));
  for (int h = 0; h < SUBGROUP_COUNT; h++) {
    for (int k = 0; k < SUBGROUP_COUNT; k++) {
      if ((subgroup_mask[k] & subgroup_mask[h]) != subgroup_mask[k]) {
        continue;
      }
      for (int size = 1; size <= BOARD_SIDE; size++) {
        int idx = orbit_idx_by_size[h][size];

        if (idx != 0xff) {
          count_suborbits(subgroup_orbits[h].orbit[idx].bb, k,
              decomp_by_size[h][k][size]);
        }
      }
    }
  }
}

static unsigned char stabilizer(unsigned char group_mask, Bitboard subset);

static SubsetList build_canonical_subsets(Bitboard orbit, int max_pieces,
    unsigned char group_mask)
{
  SubsetList list;

  memset(&list, 0, sizeof(list));
  for (Bitboard sub = orbit; sub; sub = (sub - 1) & orbit) {
    if (bitcount(sub) <= max_pieces && canonical_bb(sub, group_mask) == sub) {
      unsigned char sub_stabilizer;
      int j;

      if (list.n >= MAX_SUBSETS) {
        fprintf(stderr, "too many canonical subsets in orbit\n");
        exit(1);
      }
      sub_stabilizer = stabilizer(group_mask, sub);
      j = list.n++;
      while (j > 0 && list.subset[j - 1] > sub) {
        list.subset[j] = list.subset[j - 1];
        list.stabilizer[j] = list.stabilizer[j - 1];
        j--;
      }
      list.subset[j] = sub;
      list.stabilizer[j] = sub_stabilizer;
    }
  }
  return list;
}

void init(void)
{
  if (initialized) {
    return;
  }
  for (int t = 0; t < D8_SIZE; t++) {
    for (int sq = 0; sq < BOARD_SIZE; sq++) {
      map[t][sq] = transform_square_raw(sq, t);
    }
  }
  for (int i = 0; i < SUBGROUP_COUNT; i++) {
    subgroup_orbits[i] = build_empty_orbits(subgroup_mask[i]);
  }
  build_decomposition_tables();
  for (int s = 0; s < SUBGROUP_COUNT; s++) {
    for (int o = 0; o < subgroup_orbits[s].n; o++) {
      for (int max_pieces = 0; max_pieces <= BOARD_SIDE; max_pieces++) {
        subset_cache[s][o][max_pieces] = build_canonical_subsets(
            subgroup_orbits[s].orbit[o].bb, max_pieces, subgroup_mask[s]);
      }
    }
  }
  build_completion_tables();
  initialized = 1;
}

static void validate_mult(int n, const int mult[])
{
  int total = 0;

  if (n < 0 || n > MAX_GROUPS) {
    fprintf(stderr, "invalid number of piece groups: %d\n", n);
    exit(1);
  }
  for (int i = 0; i < n; i++) {
    if (mult[i] < 1) {
      fprintf(stderr, "invalid multiplicity %d for group %d\n", mult[i], i);
      exit(1);
    }
    total += mult[i];
  }
  if (total > MAX_PIECES) {
    fprintf(stderr, "too many pieces: %d\n", total);
    exit(1);
  }
}

static Context make_context(int n, const int mult[])
{
  Context ctx;

  init();
  validate_mult(n, mult);
  memset(&ctx, 0, sizeof(ctx));
  ctx.n = n;
  for (int i = 0; i < n; i++) {
    ctx.mult[i] = mult[i];
    ctx.total += mult[i];
  }
  return ctx;
}

static void free_context(Context *ctx)
{
  memset(ctx, 0, sizeof(*ctx));
}

static OrbitList make_orbits(unsigned char group_mask, Bitboard occ)
{
  OrbitList list;
  const OrbitList *empty = &subgroup_orbits[subgroup_index(group_mask)];

  memset(&list, 0, sizeof(list));
  for (int i = 0; i < empty->n; i++) {
    Bitboard orbit = empty->orbit[i].bb;

    if (orbit & occ) {
      if ((orbit & occ) != orbit) {
        fprintf(stderr, "internal error: occupancy is not subgroup-invariant\n");
        exit(1);
      }
      continue;
    }
    list.orbit[list.n].bb = orbit;
    list.orbit[list.n].size = empty->orbit[i].size;
    list.orbit[list.n].min_sq = empty->orbit[i].min_sq;
    list.orbit[list.n].cache_idx = empty->orbit[i].cache_idx;
    list.n++;
  }
  return list;
}

static Bitboard canonical_bb(Bitboard bb, unsigned char group_mask)
{
  Bitboard best = 0;
  int have_best = 0;

  for (int t = 0; t < D8_SIZE; t++) {
    if (group_mask & (1u << t)) {
      Bitboard cur = transform_bb(bb, t);

      if (!have_best || cur < best) {
        best = cur;
        have_best = 1;
      }
    }
  }
  return best;
}

static Bitboard canonicalize_target(Bitboard target[], int n,
    unsigned char group_mask, Bitboard subset)
{
  Bitboard best = 0;
  int best_t = -1;

  for (int t = 0; t < D8_SIZE; t++) {
    if (group_mask & (1u << t)) {
      Bitboard cur = transform_bb(subset, t);

      if (best_t < 0 || cur < best) {
        best = cur;
        best_t = t;
      }
    }
  }

  if (best_t < 0) {
    abort();
  }
  if (best != subset) {
    for (int g = 0; g < n; g++) {
      target[g] = transform_bb(target[g], best_t);
    }
  }
  return best;
}

static const SubsetList *canonical_subsets(unsigned char group_mask,
    const Orbit *orbit, int max_pieces)
{
  int max = max_pieces;

  if (max > orbit->size) {
    max = orbit->size;
  }
  return &subset_cache[subgroup_index(group_mask)][orbit->cache_idx][max];
}

static unsigned char stabilizer(unsigned char group_mask, Bitboard subset)
{
  unsigned char out = 0;

  for (int t = 0; t < D8_SIZE; t++) {
    if ((group_mask & (1u << t)) && transform_bb(subset, t) == subset) {
      out |= (unsigned char)(1u << t);
    }
  }
  return out;
}

static Bitboard remaining_allow(Bitboard allow, const OrbitList *orbits,
    int orbit_idx)
{
  Bitboard blocked = 0;

  for (int i = 0; i <= orbit_idx; i++) {
    blocked |= orbits->orbit[i].bb;
  }
  return allow & ~blocked;
}

static uint64_t count_state(Context *ctx, unsigned char group_mask,
    Bitboard occ, Bitboard allow, int g, int r);

static uint64_t count_compact(unsigned char group_mask,
    const unsigned char empty_by_size[],
    const unsigned char allow_by_size[], uint32_t rem_sig);

static uint64_t count_after_subset(Context *ctx, Bitboard occ, int g, int r,
    const OrbitList *orbits, int orbit_idx, Bitboard allow, Bitboard subset,
    unsigned char subset_stabilizer)
{
  int used = bitcount(subset);
  unsigned char new_group = subset_stabilizer;
  Bitboard new_occ = occ | subset;
  int new_r = r - used;
  Bitboard new_allow = 0;

  if (new_r > 0) {
    new_allow = remaining_allow(allow, orbits, orbit_idx);
  }
  return count_state(ctx, new_group, new_occ, new_allow, g, new_r);
}

static void make_memo_counts(const OrbitList *orbits, Bitboard allow,
    unsigned char empty_by_size[], unsigned char allow_by_size[])
{
  memset(empty_by_size, 0, BOARD_SIDE + 1);
  memset(allow_by_size, 0, BOARD_SIDE + 1);

  for (int i = 0; i < orbits->n; i++) {
    const Orbit *orbit = &orbits->orbit[i];

    empty_by_size[orbit->size]++;
    if ((orbit->bb & ~allow) == 0) {
      allow_by_size[orbit->size]++;
    } else if (orbit->bb & allow) {
      fprintf(stderr, "internal error: allow mask splits a subgroup orbit\n");
      exit(1);
    }
  }
}

static uint32_t make_rem_sig_from_context(const Context *ctx, int g, int r)
{
  uint32_t sig;
  int len;

  if (r == 0) {
    g++;
    if (g == ctx->n) {
      return 0;
    }
    r = ctx->mult[g];
  }

  len = ctx->n - g;
  sig = (uint32_t)len;
  sig |= (uint32_t)r << 4;
  for (int i = 1; i < len; i++) {
    sig |= (uint32_t)ctx->mult[g + i] << (4 * (i + 1));
  }
  return sig;
}

static int rem_len(uint32_t sig)
{
  return (int)(sig & 0xf);
}

static int rem_at(uint32_t sig, int idx)
{
  return (int)((sig >> (4 * (idx + 1))) & 0xf);
}

static uint32_t rem_after_use(uint32_t sig, int used)
{
  int len = rem_len(sig);
  int r = rem_at(sig, 0) - used;
  uint32_t out;

  if (r > 0) {
    out = (sig & ~((uint32_t)0xf << 4)) | ((uint32_t)r << 4);
    return out;
  }

  out = (uint32_t)(len - 1);
  for (int i = 1; i < len; i++) {
    out |= (uint32_t)rem_at(sig, i) << (4 * i);
  }
  return out;
}

static CountEntry *find_count_entry(unsigned char group_mask, uint32_t rem_sig,
    const unsigned char empty_by_size[], const unsigned char allow_by_size[],
    int *found)
{
  *found = 0;
  for (size_t i = 0; i < count_table_len; i++) {
    CountEntry *entry = &count_table[i];

    if (entry->group_mask == group_mask && entry->rem_sig == rem_sig &&
        memcmp(entry->empty_by_size, empty_by_size, BOARD_SIDE + 1) == 0 &&
        memcmp(entry->allow_by_size, allow_by_size, BOARD_SIDE + 1) == 0) {
      *found = 1;
      return entry;
    }
  }
  if (count_table_len == count_table_cap) {
    size_t new_cap = count_table_cap ? 2 * count_table_cap : 65536;
    CountEntry *new_table = realloc(count_table, new_cap * sizeof(*new_table));

    if (!new_table) {
      fprintf(stderr, "out of memory while building completion table\n");
      exit(1);
    }
    count_table = new_table;
    count_table_cap = new_cap;
  }
  CountEntry *entry = &count_table[count_table_len++];
  entry->group_mask = group_mask;
  entry->rem_sig = rem_sig;
  memcpy(entry->empty_by_size, empty_by_size, BOARD_SIDE + 1);
  memcpy(entry->allow_by_size, allow_by_size, BOARD_SIDE + 1);
  entry->count = UINT64_MAX;
  return entry;
}

static void decompose_counts(int h, int k, const unsigned char old_counts[],
    unsigned char new_counts[])
{
  memset(new_counts, 0, BOARD_SIDE + 1);
  for (int old_size = 1; old_size <= BOARD_SIDE; old_size++) {
    for (int new_size = 1; new_size <= BOARD_SIDE; new_size++) {
      new_counts[new_size] += (unsigned char)(old_counts[old_size] *
          decomp_by_size[h][k][old_size][new_size]);
    }
  }
}

static uint64_t count_compact(unsigned char group_mask,
    const unsigned char empty_by_size[],
    const unsigned char allow_by_size[], uint32_t rem_sig)
{
  int found;
  CountEntry *entry;
  int h;
  int r;
  uint64_t total = 0;

  if (rem_len(rem_sig) == 0) {
    return 1;
  }

  entry = find_count_entry(group_mask, rem_sig, empty_by_size, allow_by_size,
      &found);
  if (found) {
    if (entry->count == UINT64_MAX) {
      fprintf(stderr, "internal error: recursive completion-count cycle\n");
      exit(1);
    }
    return entry->count;
  }
  if (!prebuilding_counts) {
    fprintf(stderr, "internal error: completion table miss\n");
    exit(1);
  }

  h = subgroup_index(group_mask);
  r = rem_at(rem_sig, 0);

  for (int size = BOARD_SIDE; size >= 1; size--) {
    int orbit_idx;
    const SubsetList *subsets;

    if (allow_by_size[size] == 0) {
      continue;
    }
    orbit_idx = orbit_idx_by_size[h][size];
    if (orbit_idx == 0xff) {
      continue;
    }
    subsets = canonical_subsets(group_mask,
        &subgroup_orbits[h].orbit[orbit_idx], r);

    for (int pos = 1; pos <= allow_by_size[size]; pos++) {
      for (int j = 0; j < subsets->n; j++) {
        unsigned char new_empty[BOARD_SIDE + 1];
        unsigned char new_allow[BOARD_SIDE + 1];
        unsigned char occupied[BOARD_SIDE + 1];
        unsigned char remaining_allow[BOARD_SIDE + 1];
        int used = bitcount(subsets->subset[j]);
        uint32_t new_sig = rem_after_use(rem_sig, used);
        int k = subgroup_index(subsets->stabilizer[j]);

        decompose_counts(h, k, empty_by_size, new_empty);
        count_suborbits(subsets->subset[j], k, occupied);
        for (int s = 1; s <= BOARD_SIDE; s++) {
          new_empty[s] -= occupied[s];
        }

        if (used < r) {
          memset(remaining_allow, 0, sizeof(remaining_allow));
          for (int s = 1; s <= BOARD_SIDE; s++) {
            if (s < size) {
              remaining_allow[s] = allow_by_size[s];
            } else if (s == size) {
              remaining_allow[s] = (unsigned char)(allow_by_size[s] - pos);
            }
          }
          decompose_counts(h, k, remaining_allow, new_allow);
        } else {
          memcpy(new_allow, new_empty, sizeof(new_allow));
        }

        total += count_compact(subsets->stabilizer[j], new_empty, new_allow,
            new_sig);
      }
    }
  }

  entry->count = total;
  return total;
}

static uint32_t pack_parts(const int parts[], int len)
{
  uint32_t sig = (uint32_t)len;

  for (int i = 0; i < len; i++) {
    sig |= (uint32_t)parts[i] << (4 * (i + 1));
  }
  return sig;
}

static void build_completion_for_parts(const int parts[], int len)
{
  unsigned char empty_by_size[BOARD_SIDE + 1];
  unsigned char allow_by_size[BOARD_SIDE + 1];
  int full = subgroup_index(FULL_D8);

  memset(empty_by_size, 0, sizeof(empty_by_size));
  for (int i = 0; i < subgroup_orbits[full].n; i++) {
    empty_by_size[subgroup_orbits[full].orbit[i].size]++;
  }
  memcpy(allow_by_size, empty_by_size, sizeof(allow_by_size));
  (void)count_compact(FULL_D8, empty_by_size, allow_by_size,
      pack_parts(parts, len));
}

static void gen_compositions(int remaining, int parts[], int len)
{
  if (remaining == 0) {
    build_completion_for_parts(parts, len);
    return;
  }

  for (int p = 1; p <= remaining; p++) {
    parts[len] = p;
    gen_compositions(remaining - p, parts, len + 1);
  }
}

static void build_completion_tables(void)
{
  int parts[MAX_PIECES];

  prebuilding_counts = 1;
  for (int total = 1; total <= MAX_PIECES; total++) {
    gen_compositions(total, parts, 0);
  }
  prebuilding_counts = 0;
}

static uint64_t count_state(Context *ctx, unsigned char group_mask,
    Bitboard occ, Bitboard allow, int g, int r)
{
  OrbitList orbits;
  unsigned char empty_by_size[BOARD_SIDE + 1];
  unsigned char allow_by_size[BOARD_SIDE + 1];
  uint32_t rem_sig;

  if (r == 0) {
    g++;
    if (g == ctx->n) {
      return 1;
    }
    r = ctx->mult[g];
    allow = ~occ;
  }

  orbits = make_orbits(group_mask, occ);
  make_memo_counts(&orbits, allow, empty_by_size, allow_by_size);
  rem_sig = make_rem_sig_from_context(ctx, g, r);
  return count_compact(group_mask, empty_by_size, allow_by_size, rem_sig);
}

static int fill_groups_from_squares(int n, const int mult[], const int sq[],
    Bitboard group[])
{
  Bitboard occ = 0;
  int off = 0;

  for (int g = 0; g < n; g++) {
    group[g] = 0;
    for (int i = 0; i < mult[g]; i++) {
      int s = sq[off++];
      Bitboard bit;

      if (s < 0 || s >= BOARD_SIZE) {
        return 0;
      }
      bit = (Bitboard)1 << s;
      if (occ & bit) {
        return 0;
      }
      occ |= bit;
      group[g] |= bit;
    }
  }
  return 1;
}

static uint64_t rank_state(Context *ctx, Bitboard target[],
    unsigned char group_mask, Bitboard occ, Bitboard allow, int g, int r,
    int *valid)
{
  OrbitList orbits;
  int actual_orbit = -1;
  Bitboard actual_subset = 0;
  uint64_t rank = 0;

  if (r == 0) {
    g++;
    if (g == ctx->n) {
      return 0;
    }
    r = ctx->mult[g];
    allow = ~occ;
  }

  orbits = make_orbits(group_mask, occ);

  for (int i = 0; i < orbits.n; i++) {
    if ((orbits.orbit[i].bb & ~allow) && (target[g] & orbits.orbit[i].bb)) {
      *valid = 0;
      return 0;
    }
  }

  for (int i = 0; i < orbits.n; i++) {
    Bitboard here = target[g] & orbits.orbit[i].bb;

    if (orbits.orbit[i].bb & ~allow) {
      continue;
    }
    if (here) {
      actual_orbit = i;
      actual_subset = here;
      break;
    }
  }
  if (actual_orbit < 0 || bitcount(actual_subset) > r) {
    *valid = 0;
    return 0;
  }
  actual_subset = canonicalize_target(target, ctx->n, group_mask,
      actual_subset);

  for (int i = 0; i <= actual_orbit; i++) {
    const SubsetList *subsets = canonical_subsets(group_mask,
        &orbits.orbit[i], r);

    if (orbits.orbit[i].bb & ~allow) {
      continue;
    }
    for (int j = 0; j < subsets->n; j++) {
      if (i == actual_orbit && subsets->subset[j] == actual_subset) {
        rank += rank_state(ctx, target, subsets->stabilizer[j],
            occ | actual_subset,
            r - bitcount(actual_subset) > 0
                ? remaining_allow(allow, &orbits, actual_orbit)
                : 0,
            g, r - bitcount(actual_subset),
            valid);
        return rank;
      }
      if (i < actual_orbit ||
          (i == actual_orbit && subsets->subset[j] < actual_subset)) {
        rank += count_after_subset(ctx, occ, g, r, &orbits, i, allow,
            subsets->subset[j], subsets->stabilizer[j]);
      }
    }
  }

  *valid = 0;
  return 0;
}

uint64_t rank(int n, int mult[], int sq[])
{
  Context ctx = make_context(n, mult);
  Bitboard group[MAX_GROUPS];
  int valid = 1;
  uint64_t rk;

  if (!fill_groups_from_squares(n, mult, sq, group)) {
    fprintf(stderr, "invalid placement passed to rank\n");
    exit(1);
  }

  if (n == 0) {
    free_context(&ctx);
    return 0;
  }

  rk = rank_state(&ctx, group, FULL_D8, 0, ~(Bitboard)0, 0, mult[0], &valid);
  if (!valid) {
    fprintf(stderr, "internal error: placement is not recursively canonical\n");
    exit(1);
  }

  free_context(&ctx);
  return rk;
}

uint64_t count_unique_positions(int n, int mult[])
{
  Context ctx = make_context(n, mult);
  uint64_t count = n == 0 ? 1 : count_state(&ctx, FULL_D8, 0, ~(Bitboard)0, 0,
      mult[0]);

  free_context(&ctx);
  return count;
}

static void unrank_state(Context *ctx, uint64_t *rk, Bitboard group[],
    unsigned char group_mask, Bitboard occ, Bitboard allow, int g, int r)
{
  OrbitList orbits;

  if (r == 0) {
    g++;
    if (g == ctx->n) {
      return;
    }
    r = ctx->mult[g];
    allow = ~occ;
  }

  orbits = make_orbits(group_mask, occ);
  for (int i = 0; i < orbits.n; i++) {
    const SubsetList *subsets = canonical_subsets(group_mask,
        &orbits.orbit[i], r);

    if (orbits.orbit[i].bb & ~allow) {
      continue;
    }
    for (int j = 0; j < subsets->n; j++) {
      uint64_t count = count_after_subset(ctx, occ, g, r, &orbits, i, allow,
          subsets->subset[j], subsets->stabilizer[j]);

      if (*rk >= count) {
        *rk -= count;
        continue;
      }

      group[g] |= subsets->subset[j];
      unrank_state(ctx, rk, group, subsets->stabilizer[j],
          occ | subsets->subset[j],
          r - bitcount(subsets->subset[j]) > 0
              ? remaining_allow(allow, &orbits, i)
              : 0,
          g, r - bitcount(subsets->subset[j]));
      return;
    }
  }

  fprintf(stderr, "internal error: rank not consumed during unrank\n");
  exit(1);
}

Bitboard unrank(int n, int mult[], uint64_t rk, int out[])
{
  Context ctx = make_context(n, mult);
  uint64_t count = n == 0 ? 1 : count_state(&ctx, FULL_D8, 0, ~(Bitboard)0, 0,
      mult[0]);
  Bitboard group[MAX_GROUPS] = { 0 };
  Bitboard occ = 0;
  int off = 0;

  if (rk >= count) {
    fprintf(stderr, "rank %" PRIu64 " is out of range; maximum is %" PRIu64
        "\n", rk, count ? count - 1 : 0);
    exit(1);
  }

  if (n > 0) {
    unrank_state(&ctx, &rk, group, FULL_D8, 0, ~(Bitboard)0, 0, mult[0]);
  }

  for (int g = 0; g < n; g++) {
    Bitboard b = group[g];

    while (b) {
      int sq = take_square(&b);
      out[off++] = sq;
      occ |= (Bitboard)1 << sq;
    }
  }

  free_context(&ctx);
  return occ;
}

static void print_position(int n, const int mult[], const int sq[])
{
  int off = 0;

  printf("[");
  for (int g = 0; g < n; g++) {
    printf("%s{", g ? ", " : "");
    for (int i = 0; i < mult[g]; i++) {
      printf("%s%d", i ? ", " : "", sq[off++]);
    }
    printf("}");
  }
  printf("]");
}

static int test_case(int n, int mult[], int sq[])
{
  int total = 0;
  uint64_t count;
  uint64_t rk;
  int out[BOARD_SIZE];
  uint64_t rk2;

  for (int i = 0; i < n; i++) {
    total += mult[i];
  }

  count = count_unique_positions(n, mult);
  rk = rank(n, mult, sq);
  (void)unrank(n, mult, rk, out);
  rk2 = rank(n, mult, out);

  print_position(n, mult, sq);
  printf(" -> %" PRIu64 " unique positions, rank %" PRIu64 " -> ", count, rk);
  print_position(n, mult, out);
  printf("\n");

  if (rk >= count || rk != rk2) {
    fprintf(stderr, "round trip failed: rank=%" PRIu64 ", rank2=%" PRIu64
        ", count=%" PRIu64 "\n", rk, rk2, count);
    return 0;
  }

  for (int t = 0; t < D8_SIZE; t++) {
    int transformed[BOARD_SIZE];

    for (int i = 0; i < total; i++) {
      transformed[i] = map[t][sq[i]];
    }
    if (rank(n, mult, transformed) != rk) {
      fprintf(stderr, "symmetry-invariance check failed for transform %d\n", t);
      return 0;
    }
  }

  for (int i = 0; i < total; i++) {
    if (out[i] < 0 || out[i] >= BOARD_SIZE) {
      return 0;
    }
  }
  return 1;
}

int main(int argc, char *argv[])
{
  int ok = 1;

  (void)argc;
  (void)argv;

  init();

  {
    int mult[] = { 1 };
    int sq[] = { 0 };
    ok &= test_case(1, mult, sq);
  }
  {
    int mult[] = { 2 };
    int sq[] = { 0, 63 };
    ok &= test_case(1, mult, sq);
  }
  {
    int mult[] = { 1, 1 };
    int sq[] = { 0, 9 };
    ok &= test_case(2, mult, sq);
  }
  {
    int mult[] = { 2, 1 };
    int sq[] = { 0, 7, 28 };
    ok &= test_case(2, mult, sq);
  }

  return ok ? 0 : 1;
}
