/* Generalized schedule enumeration for f(6) in C.
 *
 * Steps: directed cycles (min-first canonical tuples) on 2..6 men.
 * State: identity start; budget <= 30 moved-man slots; <= 5 moves/man;
 * no partner revisit. Pruning (all SOUND for max-preservation):
 *  - new men in a step must be exactly the next unused labels (as a set);
 *  - backward-commute: reject a step lex-smaller (by step index) than any
 *    suffix step it is man-disjoint with;
 *  - per-man move cap and budget cap.
 * Evaluation (exact stable-matching count of the bottom-completed
 * read-off instance) only at maximal nodes (no valid extension).
 *
 * Usage: gen_enum <budget> <shard> <nshards>   (shard on step at depth 1)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define N 6
#define MAXSTEPS 480
#define MAXSEQ 15

static int step_men[MAXSTEPS][N], step_k[MAXSTEPS], step_mask[MAXSTEPS];
static int nsteps = 0;

static int perms[720][N], nperms = 0;
static void gen_perms(int *cur, int used, int depth) {
    if (depth == N) { memcpy(perms[nperms++], cur, sizeof(int) * N); return; }
    for (int i = 0; i < N; i++) if (!(used >> i & 1)) {
        cur[depth] = i; gen_perms(cur, used | 1 << i, depth + 1);
    }
}

static void gen_steps(void) {
    /* all subsets size k, all cyclic orders with min element first */
    for (int k = 2; k <= N; k++) {
        int idx[N];
        for (int sub = 0; sub < (1 << N); sub++) {
            if (__builtin_popcount(sub) != k) continue;
            int cnt = 0;
            for (int i = 0; i < N; i++) if (sub >> i & 1) idx[cnt++] = i;
            /* permute idx[1..k-1] */
            int pos[N]; for (int i = 0; i < k - 1; i++) pos[i] = i;
            int rest[N];
            /* simple recursive permutation via Heap's alg (iterative here) */
            int c[N]; for (int i = 0; i < k - 1; i++) c[i] = 0;
            for (int i = 0; i < k - 1; i++) rest[i] = idx[i + 1];
            for (;;) {
                step_men[nsteps][0] = idx[0];
                int mask = 1 << idx[0];
                for (int i = 0; i < k - 1; i++) {
                    step_men[nsteps][i + 1] = rest[i];
                    mask |= 1 << rest[i];
                }
                step_k[nsteps] = k; step_mask[nsteps] = mask; nsteps++;
                /* next permutation of rest (Heap) */
                int i = 0;
                while (i < k - 1) {
                    if (c[i] < i) {
                        int j = (i % 2 == 0) ? 0 : c[i];
                        int t = rest[j]; rest[j] = rest[i]; rest[i] = t;
                        c[i]++; i = 0; break;
                    } else { c[i] = 0; i++; }
                }
                if (i >= k - 1) break;
            }
        }
    }
}

static int mu[N], moves_used[N], mvis[N], wvis[N];
static int mtraj[N][N], mlen[N], wtraj[N][N], wlen[N];
static int seq[MAXSEQ], depth = 0;
static long long nodes = 0, leaves = 0;
static int best = 0;
static int budget_cap, shard, nshards;
static long long shard_ctr = 0;

static int count_stable_readoff(void) {
    int mrank[N][N], wrank[N][N];
    for (int m = 0; m < N; m++) {
        int pos = 0;
        for (int i = 0; i < mlen[m]; i++) mrank[m][mtraj[m][i]] = pos++;
        for (int w = 0; w < N; w++)
            if (!(mvis[m] >> w & 1)) mrank[m][w] = pos++;
    }
    for (int w = 0; w < N; w++) {
        int pos = 0;
        for (int i = wlen[w] - 1; i >= 0; i--) wrank[w][wtraj[w][i]] = pos++;
        for (int m = 0; m < N; m++)
            if (!(wvis[w] >> m & 1)) wrank[w][m] = pos++;
    }
    int cnt = 0;
    for (int p = 0; p < nperms; p++) {
        const int *pm = perms[p];
        int inv[N];
        for (int m = 0; m < N; m++) inv[pm[m]] = m;
        int ok = 1;
        for (int m = 0; m < N && ok; m++) {
            int thr = mrank[m][pm[m]];
            if (!thr) continue;
            for (int w = 0; w < N; w++) {
                if (mrank[m][w] < thr && wrank[w][m] < wrank[w][inv[w]]) {
                    ok = 0; break;
                }
            }
        }
        cnt += ok;
    }
    return cnt;
}

static void dfs(int used, int maxused) {
    nodes++;
    int extended = 0;
    for (int s = 0; s < nsteps; s++) {
        int k = step_k[s];
        if (used + k > budget_cap) continue;
        /* new-men rule: new men must be exactly next labels as a set */
        int newmask = step_mask[s] & ~((1 << maxused) - 1);
        if (newmask) {
            int expect = newmask;
            /* must be contiguous from maxused */
            int nm = __builtin_popcount(newmask);
            int want = ((1 << nm) - 1) << maxused;
            if (expect != want) continue;
        }
        int bad = 0;
        for (int i = 0; i < k; i++)
            if (moves_used[step_men[s][i]] >= 5) { bad = 1; break; }
        if (bad) continue;
        /* backward-commute pruning */
        for (int d = depth - 1; d >= 0; d--) {
            int ps = seq[d];
            if (step_mask[ps] & step_mask[s]) break;
            if (ps > s) { bad = 1; break; }
        }
        if (bad) continue;
        /* validity */
        int neww[N], oldw[N];
        for (int i = 0; i < k; i++) {
            int m = step_men[s][i];
            int w = mu[step_men[s][(i + 1) % k]];
            neww[i] = w;
            if ((mvis[m] >> w & 1) || (wvis[w] >> m & 1)) { bad = 1; break; }
        }
        if (bad) continue;
        if (depth == 1 && nshards > 1) {
            if ((shard_ctr++ % nshards) != (long long)shard) { extended = 1; continue; }
        }
        /* apply */
        for (int i = 0; i < k; i++) oldw[i] = mu[step_men[s][i]];
        for (int i = 0; i < k; i++) {
            int m = step_men[s][i], w = neww[i];
            mu[m] = w; moves_used[m]++;
            mvis[m] |= 1 << w; wvis[w] |= 1 << m;
            mtraj[m][mlen[m]++] = w; wtraj[w][wlen[w]++] = m;
        }
        seq[depth++] = s;
        extended = 1;
        int nmx = maxused;
        for (int i = 0; i < k; i++)
            if (step_men[s][i] >= nmx) nmx = step_men[s][i] + 1;
        dfs(used + k, nmx);
        depth--;
        for (int i = k - 1; i >= 0; i--) {
            int m = step_men[s][i], w = neww[i];
            mlen[m]--; wlen[w]--;
            mvis[m] &= ~(1 << w); wvis[w] &= ~(1 << m);
            moves_used[m]--; mu[m] = oldw[i];
        }
    }
    if (!extended) {
        leaves++;
        int c = count_stable_readoff();
        if (c > best) {
            best = c;
            printf("new best %d at depth %d: steps", c, depth);
            for (int d = 0; d < depth; d++) {
                printf(" (");
                for (int i = 0; i < step_k[seq[d]]; i++)
                    printf("%s%d", i ? "," : "", step_men[seq[d]][i]);
                printf(")");
            }
            printf("\n");
            fflush(stdout);
        }
    }
}

int main(int argc, char **argv) {
    budget_cap = atoi(argv[1]);
    shard = argc > 2 ? atoi(argv[2]) : 0;
    nshards = argc > 3 ? atoi(argv[3]) : 1;
    int cur[N];
    gen_perms(cur, 0, 0);
    gen_steps();
    for (int m = 0; m < N; m++) {
        mu[m] = m; mvis[m] = 1 << m; wvis[m] = 1 << m;
        mtraj[m][0] = m; mlen[m] = 1; wtraj[m][0] = m; wlen[m] = 1;
    }
    dfs(0, 0);
    printf("budget=%d shard=%d/%d nodes=%lld maximal=%lld best=%d\n",
           budget_cap, shard, nshards, nodes, leaves, best);
    return 0;
}
