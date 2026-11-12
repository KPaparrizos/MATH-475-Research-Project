/*
    This file executes an exhastive check of
    Frankl's Conjecture, Conjectures 2, 3, and
    4 from Poonen, and the S2-Frankl Conjecture
    from Cui & Hu on universes up to size THRESH = 6
    whose blocks are singletons. Each family is tested
    once as it is and once with the empty set removed.
*/

/*
    Note: each set A is represented as a bit string,
    where the ith bit is 1 exactly when i is
    contained in A. We let A, the name of the set,
    correspond to the integer value of this bit string.

*/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/*
    Unsigned 64-bit integer type meant to
    represent a family F that is a subset of P(U).
    The bit A is 1 exactly when A is contained in F.
    Note |F| <= |P(U)| = 2^m. Since we are
    considering m <= 6, |F| <= 2^6 = 64, so a 64-bit
    integer is sufficient.
*/

typedef uint64_t family_t;

// Maximum size of universes being checked
#define THRESH 6

/*
    m represent the size of the universe
    being considered. U is the universe [m] itself
    (i.e. the first m bits are 1s, so U =
    2^m - 1)
*/
static int m, U;

/*
    For each i, contains[i] represents the family of
    all sets containing i. Since we are considering m <= 6,
    i <= 6.
*/
static family_t contains[THRESH];

// Represents the family of all singletons in P(U).
static family_t singletons;

// enums to represent the conjectures under consideration.
// NCHECK is 5, the number of conjectures we are considering.
enum conjecture
{
    FRANKL,
    CONJ2,
    CONJ3,
    CONJ4,
    CUIHU2,
    NCHECK
};

// Array to map enums to the names of the conjectures they represent
static const char *name[NCHECK] = {"Frankl", "Conj2", "Conj3", "Conj4", "S2(CuiHu)"};

// Array to count how many families have been tested for each conjecture
static uint64_t tested[NCHECK];

// Array to count how many families failed for each conjecture
static uint64_t failed[NCHECK];

// Counts number of seperating families generated
static uint64_t n_families,

    // Array to track families that were near misses with
    // slack s = 1 or 2 (s = 2 * max{|Fa| for a in U} - |F|)
    near_miss[3];

// Names for CSV files
static const char *csv_name[NCHECK] = {"frankl", "conj2", "conj3", "conj4", "s2"};

// CSV file outputs
static FILE *csv_summary = NULL;
static FILE *csv_families = NULL;
// 1 to write every tested family and not just failures or near misses, 0 otherwise
static int csv_all = 0;

// Returns number of members in a family F, i.e. |F|
// (__builtin_popcountll(x) returns the number of 1 bits in x).
static int popc(family_t x)
{
    return __builtin_popcountll(x);
}

// Prints failing family G in hexadecinal, along with the conjecture it failed
static void report_violation(int check, family_t G)
{
    printf("  VIOLATION of %s, family bitmask 0x%016llx\n", name[check], (unsigned long long)G);
}

// Writes on CSV row for a family G, where verdict[c] is 1 if c holds, 0
// if c fails, and -1 if the hypothesis is not met
static void write_family_row(family_t G, int N, const int f[], int top, int power,
                             const int verdict[], const char *reason)
{
    FILE *o = csv_families;

    fprintf(o, "%d,%d,%d,%d,%d,%d,%s", m, (int)(G & 1), N, top, 2 * top - N, power, reason);

    for (int c = 0; c < NCHECK; c++)
    {
        if (verdict[c] < 0)
            fputs(",", o);
        else
            fprintf(o, ",%d", verdict[c]);
    }

    fputs(",\"", o);

    for (int i = 0; i < m; i++)
    {
        fprintf(o, i ? ";%d" : "%d", f[i]);
    }

    fputs("\",\"", o);

    int first = 1;

    for (int A = 0; A <= U; A++)
        if ((G >> A) & 1)
        {
            fputs(first ? "{" : ";{", o);
            first = 0;
            int firstel = 1;
            for (int i = 0; i < m; i++)
                if ((A >> i) & 1)
                {
                    fprintf(o, firstel ? "%d" : ",%d", i);
                    firstel = 0;
                }
            fputs("}", o);
        }

    fprintf(o, "\",0x%016llx\n", (unsigned long long)G);
}

// Returns 1 if a the blocks of family F are singletons, and 0 otherwise
static int is_separating(family_t F)
{
    family_t col[THRESH];
    // Loop through all i in U
    for (int i = 0; i < m; i++)
    {
        /*
            Stores all members A in F that contain i, taking the
            bitwise and of F with contains[i], the family of all
            sets containing i
        */
        col[i] = F & contains[i];

        // If some element does not appear in any member of F,
        // return 0; [m] should always be a member
        if (!col[i])
            return 0;

        // Loop through all j in U such that j < i, if i and j in exactly the same
        // members, return 0, as these elements form a non-trivial block.
        for (int j = 0; j < i; j++)
            if (col[i] == col[j])
                return 0;
    }
    return 1;
}

// Checks if a given family G fails any conjectures
static void check_family(family_t G)
{
    int N = popc(G);
    // Frequency of each i in U
    int f[THRESH];
    // Frequency of the most frequent element in G
    int top = 0;
    // Number of abundant elements in G
    int n_ab = 0;
    // Last abundant element in G
    int x = -1;
    // Result of each check on G: 1 = holds, 0 = fails, -1 = hypothesis not met
    int verdict[NCHECK] = {-1, -1, -1, -1, -1};

    // Loop through elements in U
    for (int i = 0; i < m; i++)
    {
        // For each i in U, store the frequency of i in G
        // as the ith element of f
        f[i] = popc(G & contains[i]);

        // If i is more frequent than top, update top
        if (f[i] > top)
        {
            top = f[i];
        }

        // If i is abundant, update n_ab and set x to be i
        if (2 * f[i] >= N)
        {
            n_ab++;
            x = i;
        }
    }

    // Update tested to count that Frankl's conjecture has been tested on G
    tested[FRANKL]++;
    // Record whether G has an abundant element (if not, Frankl's conjecture
    // fails on G; failures are counted and displayed below)
    verdict[FRANKL] = (2 * top >= N);

    int power = (N == (1 << m));
    // If G is not a power set, check Conjecture 2 from Poonen
    if (!power)
    {
        // Update tested to count that Poonen's Conjecture 2 has been tested on G
        tested[CONJ2]++;
        // Record whether some i in U has frequency greater than |G| / 2 (if not,
        // Conjecture 2 fails on G; failures are counted and displayed below)
        verdict[CONJ2] = (2 * top > N);
    }

    // Check if there is exactly 1 abundant element, a condition for Poonen's
    // Conjectures 3 and 4
    if (n_ab == 1)
    {
        // Update tested to count that Poonen's Conjecture 3 has been tested on G
        tested[CONJ3]++;
        /*
            Record whether, excluding the empty set (0 bit), every member of G
            contains x (the only abundant element). If some member does not,
            Conjecture 3 fails on G; failures are counted and displayed below
        */
        verdict[CONJ3] = ((G & ~(family_t)1 & ~contains[x]) == 0);

        // Update tested to count that Poonen's Conjecture 4 has been tested on G
        tested[CONJ4]++;
        // Family containing the empty set and all members of P(U) containing x
        family_t sunflower = contains[x] | 1;
        // Family containing just {x}
        family_t just_x = (family_t)1 << (1 << x);
        /*
            Record whether G is the family containing only {x} or the family containing
            all members of P(U) containing x (which is equivalent to the implication in
            Poonen Conjecture 4). If neither, Conjecture 4 fails on G; failures are
            counted and displayed below
        */
        verdict[CONJ4] = (G == sunflower || G == just_x);
    }

    // Check if G does not contain the empty set and every member A of G
    // is such that |A| >= 2, the conditions for the S2-Frankl Conjecture
    if (!(G & 1) && !(G & singletons))
    {
        // Update tested to count that the S2-Frankl Conjecture has been tested on G
        tested[CUIHU2]++;
        // Counts how many i in U have frequency greater than |G| / 2
        int strict = 0;
        // Loop through all i in U
        for (int i = 0; i < m; i++)
        {
            // If some element i has frequency greater than |G| / 2, update strict
            if (2 * f[i] > N)
            {
                strict++;
            }
        }
        // Record whether at least 2 elements in G have frequency greater than |G| / 2
        // (if not, the S2-Frankl Conjecture fails on G; failures are counted and displayed below)
        verdict[CUIHU2] = (strict >= 2);
    }

    // For every check that failed on G, update failed to count the failure
    // and display the violation
    int any_fail = 0;
    for (int c = 0; c < NCHECK; c++)
    {
        if (verdict[c] == 0)
        {
            failed[c]++;
            report_violation(c, G);
            any_fail = 1;
        }
    }

    // Compute slack
    int slack = 2 * top - N;
    // Skip families not containing the empty set and power sets
    // Power sets expected to have zero slack, skipping families not
    // containing empty set ensures each family counted only once
    int is_near = (G & 1) && !power && slack >= 0 && slack <= 2;
    if (is_near)
    {
        near_miss[slack]++;
    }

    // If CSV output was requested, write G as a row when it failed a check or is a
    // near-miss, or always when --all was given
    if (csv_families && (any_fail || is_near || csv_all))
    {
        write_family_row(G, N, f, top, power, verdict,
                         any_fail ? "violation" : is_near ? "near_miss"
                                                          : "checked");
    }
}

// Array containg sets in the family in the order they were chosen
static int chosen[64];
// Number of sets chosen for the family
static int n_chosen;
// For parallel computation; not used
static int split_depth = -1;
static int job = 0;
static int njobs = 1;

// Given a family F, checks if a family is seperating. If not, skips
// F. If it is, checks all conjectures on F with and without the empty set
static void visit(family_t F)
{
    if (!is_separating(F))
    {
        return;
    }

    n_families++;
    check_family(F);
    check_family(F & ~(family_t)1);
}

// Recursively contructs all union closed families in the universe U, beginning
// with the subset U and progressing down (i.e. to U-1, U-2, ...)
static void rec(int S, family_t F, uint64_t path, int depth)
{
    // Parallelism filter to ensure jobs do not do overlapping work
    if (depth == split_depth && (int)(path % (uint64_t)njobs) != job)
    {
        return;
    }

    // If every subset has been decided, F is complete, so call visit and then return
    if (S < 0)
    {
        visit(F);
        return;
    }

    // If S is not empty or the universe (which are both already contained in
    // every family), calls rec with the next lowest subset (leaving S out)
    if (S != 0 && S != U)
    {
        rec(S - 1, F, path * 2, depth + 1);
    }

    // Checks if adding S would keep the family F union closed. If not, return.
    for (int k = 0; k < n_chosen; k++)
    {
        if (!((F >> (S | chosen[k])) & 1))
        {
            return;
        }
    }

    // Add S to chosen and increase n_chosen by 1
    chosen[n_chosen++] = S;
    // Add S to the family and call rec with the next lowest subset
    rec(S - 1, F | ((family_t)1 << S), path * 2 + 1, depth + 1);
    // Remove S before returning
    n_chosen--;
}

// Set up variables for universe of next size
static void setup(int mm)
{
    m = mm;
    U = (1 << m) - 1;
    singletons = 0;

    // Build contains array and singletons
    for (int i = 0; i < m; i++)
    {
        contains[i] = 0;
        for (int A = 0; A <= U; A++)
        {
            if ((A >> i) & 1)
            {
                contains[i] |= (family_t)1 << A;
            }
        }

        singletons |= (family_t)1 << (1 << i);
    }

    // Reset all counters
    memset(tested, 0, sizeof tested);
    memset(failed, 0, sizeof failed);
    memset(near_miss, 0, sizeof near_miss);
    n_families = 0;
    n_chosen = 0;
}

// Run full checks for universes of size mm
static void run(int mm)
{
    setup(mm);
    rec(U, 0, 0, 0);

    printf("\nm = %d: %llu separating union-closed families containing the empty set",
           m, (unsigned long long)n_families);

    if (njobs > 1)
    {
        printf(" (part %d of %d)", job, njobs);
    }

    printf("\n");

    for (int c = 0; c < NCHECK; c++)
    {
        printf("  %-10s hypothesis met %12llu   failures %llu\n", name[c],
               (unsigned long long)tested[c], (unsigned long long)failed[c]);
    }

    printf("  near-misses (not a power set, max frequency <= N/2 + 1): slack1 %llu  slack2 %llu\n",
           (unsigned long long)near_miss[1], (unsigned long long)near_miss[2]);

    if (csv_summary)
    {
        fprintf(csv_summary, "%d,%d,%d,%llu", m, job, njobs, (unsigned long long)n_families);

        for (int c = 0; c < NCHECK; c++)
        {
            fprintf(csv_summary, ",%llu,%llu", (unsigned long long)tested[c], (unsigned long long)failed[c]);
        }

        fprintf(csv_summary, ",%llu,%llu\n", (unsigned long long)near_miss[1], (unsigned long long)near_miss[2]);
        fflush(csv_summary);
    }
}

// Number of union closed families containing U and the empty set found by rec_all
static uint64_t count_all_uc;

// Counts every union closed family in U that contains the empty set
static void rec_all(int S, family_t F)
{
    if (S < 0)
    {
        count_all_uc++;
        return;
    }

    //
    if (S != 0 && S != U)
    {
        rec_all(S - 1, F);
    }

    for (int k = 0; k < n_chosen; k++)
    {
        if (!((F >> (S | chosen[k])) & 1))
        {
            return;
        }
    }

    chosen[n_chosen++] = S;
    rec_all(S - 1, F | ((family_t)1 << S));
    n_chosen--;
}

// Checks by definition if a family F is union closed
static int union_closed_brute(family_t F)
{
    // Loops through all sets A in F and checks if the union with
    // any set B in F is also in F
    for (int A = 0; A <= U; A++)
        if ((F >> A) & 1)
        {
            for (int B = 0; B <= U; B++)
                if ((F >> B) & 1)
                {
                    if (!((F >> (A | B)) & 1))
                    {
                        return 0;
                    }
                }
        }

    return 1;
}

// Test program for correctness
static void self_tests(void)
{
    // Checks for universe of size m = 1 to m = 4 that the generator agrees
    // with the brute force check
    for (int mm = 1; mm <= 4; mm++)
    {
        setup(mm);
        count_all_uc = 0;
        rec_all(U, 0);
        uint64_t bf = 0;
        int inner = U - 1;

        for (uint64_t mask = 0; mask < ((uint64_t)1 << inner); mask++)
        {
            family_t F = 1 | ((family_t)1 << U) | (mask << 1);
            if (union_closed_brute(F))
            {
                bf++;
            }
        }

        if (bf != count_all_uc)
        {
            printf("SELF-TEST FAILED: m=%d gen %llu brute %llu\n",
                   mm, (unsigned long long)count_all_uc, (unsigned long long)bf);
            exit(1);
        }
    }

    // Check that for universes of size m = 4 the generator
    // agrees with known results
    setup(4);
    count_all_uc = 0;
    rec_all(U, 0);

    if (count_all_uc != 2271)
    {
        printf("SELF-TEST FAILED: count 2271\n");
        exit(1);
    }

    // Verify that the checks can catch bad families
    setup(2);
    family_t bad = 1 | (1 << 1) | (1 << 2);
    check_family(bad);

    if (failed[FRANKL] != 1)
    {
        printf("SELF-TEST FAILED: bad family not flagged\n");
        exit(1);
    }

    printf("self-tests passed (the VIOLATION line above is the intended test failure)\n");
}

// Opens CSV and prepares to write to file
static FILE *open_csv(const char *prefix, const char *part, const char *suffix, const char *header)
{
    char path[512];

    snprintf(path, sizeof path, "%s%s_%s.csv", prefix, part, suffix);

    FILE *o = fopen(path, "w");

    if (!o)
    {
        perror(path);
        exit(1);
    }

    fputs(header, o);
    printf("writing %s\n", path);
    return o;
}

// Runs full program, including test, checks from m = 1 to m = 6, and writing to the CSV
int main(int argc, char **argv)
{
    int pos[3];
    int npos = 0;

    const char *prefix = NULL;

    for (int a = 1; a < argc; a++)
    {
        if (!strcmp(argv[a], "--csv") && a + 1 < argc)
        {
            prefix = argv[++a];
        }
        else if (!strcmp(argv[a], "--all"))
        {
            csv_all = 1;
        }
        else if (npos < 3)
        {
            pos[npos++] = atoi(argv[a]);
        }
        else
        {
            fprintf(stderr, "too many arguments\n");
            return 1;
        }
    }

    int top = npos >= 1 ? pos[0] : 5;

    if (top < 1 || top > THRESH)
    {
        fprintf(stderr, "m must be 1..%d\n", THRESH);
        return 1;
    }

    if (npos == 2)
    {
        fprintf(stderr, "cluster mode needs both J and K\n");
        return 1;
    }

    int cluster = (npos == 3);

    if (cluster)
    {
        job = pos[1];
        njobs = pos[2];
        split_depth = 20;
        if (njobs < 1 || job < 0 || job >= njobs)
        {
            fprintf(stderr, "need 0 <= J < K\n");
            return 1;
        }
    }

    if (csv_all && top == 6)
    {
        fprintf(stderr, "--all is too large for m = 6 (tens of billions of rows)\n");
        return 1;
    }

    if (!cluster)
    {
        self_tests();
    }

    if (prefix)
    {
        char part[64] = "";

        if (cluster)
        {
            snprintf(part, sizeof part, "_part%d", job);
        }

        char header[1024] = "m,job,njobs,families";

        for (int c = 0; c < NCHECK; c++)
        {
            strcat(header, ",");
            strcat(header, csv_name[c]);
            strcat(header, "_tested");
            strcat(header, ",");
            strcat(header, csv_name[c]);
            strcat(header, "_failed");
        }

        strcat(header, ",near_miss_slack1,near_miss_slack2\n");
        csv_summary = open_csv(prefix, part, "summary", header);
        csv_families = open_csv(prefix, part, "families",
                                "m,has_empty,N,max_freq,slack,power_set,reason,frankl,conj2,conj3,conj4,s2,freqs,members,bitmask\n");
    }

    if (cluster)
    {
        run(top);
    }
    else
    {
        for (int mm = 1; mm <= top; mm++)
        {
            run(mm);
        }
    }

    if (csv_summary)
    {
        fclose(csv_summary);
    }

    if (csv_families)
    {
        fclose(csv_families);
    }

    return 0;
}