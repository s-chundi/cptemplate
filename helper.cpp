#include <iostream>
#include <string>
#include <vector>
#include <cstdio>
#include <deque>
#include <unordered_set>
#include <cctype>
#include <unordered_map>
#include <cstring>
#include <algorithm>
#include <cassert>
#include <set>
#include <map>
#include <limits.h>
#include <sstream>
#include <stdlib.h>
#include <time.h> 
#include <cctype>
#include <cmath>
#include <bit>
#include <queue>
#include <numeric>
#include <iomanip>
// #include <ext/pb_ds/assoc_container.hpp>
// #include <ext/pb_ds/tree_policy.hpp>
// using namespace __gnu_pbds;
// #define os(T) tree<T, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update>
// #define om(T0, T1) tree<T0, T1, less<int>, rb_tree_tag, tree_order_statistics_node_update>
// #define omc(T0, T1, CMP) tree<T0, T1, CMP, rb_tree_tag, tree_order_statistics_node_update>
using namespace std;
using ll = long long;
using ul = unsigned long;
using ull = unsigned long long;
using ld = long double;
using vi = vector<int>;
using vvi = vector<vi>;
using vll = vector<ll>;
using pll = pair<ll, ll>;
using vpll = vector<pair<ll, ll>>;
using qi = queue<int>;
using pii = pair<int, int>;
using di = deque<int>;
using dpi = deque<pii>;
using vpi = vector<pii>;
using tii = tuple<int, int, int>;
using vti = vector<tii>;
using qpi = queue<pii>;
using qti = queue<tii>;
using vc = vector<char>;
using si = unordered_set<int>;
using mosi = multiset<int>;
#define lso(S) ((S) & -(S))
const int MOD = 1e9 + 7;
const int F = 1e5;
const ll INF = 1e18;


// Sieve of Erato Works for roughly 2 * 10 ^ 7
// We also get the smallest factor
struct euler{
    const static int MAXN = F;
    vi primes{};
    bool eul[MAXN]{};
    int smallest_factor[MAXN]{};

    void make_primes(){
        iota(smallest_factor, smallest_factor + MAXN, 0);
        eul[0] = true;
        eul[1] = true;
        for (ll i = 2; i < MAXN; ++i){
            if (eul[i] == false){
                primes.push_back(i);
                for (ll j = i * i; j < MAXN; j += i){
                    if (smallest_factor[j] == j){
                        smallest_factor[j] = i;
                    }
                    eul[j] = true;
                }
            }
        }
    }
};

struct suffix_automaton{
    // Suffix Automaton
    struct state{
        int len, link; // link is the suffix link
        map<char, int> next;
    };

    state st[2 * F]; // Assumes F is maxlen
    int sz = 0; int prev;

    void sa_init() { // Initially, we have only 1 state, the "". 
        st[0].len = 0;
        st[0].link = -1;
        sz++;
        prev = 0;
    }

    void add_char(char c) { 
        int cur = sz++;                             // Update size and length of current char
        st[cur].len = st[prev].len + 1;
        int p = prev;
        while (p != -1 && !st[p].next.count(c)){    // adding transition p -> cur 
            st[p].next[c] = cur;                    // and have p follow the suffix link
            p = st[p].link;
        }
        if (p == -1) {                              // Should add the suffix link to root
            st[cur].link = 0;
        } else {
            int q = st[p].next[c];                  // There is a transition, follow it
            if (st[p].len + 1 == st[q].len) {       // q is exactly what we've been looking for
                st[cur].link = q;
            } else {
                int clone = sz++;                   // q is not what I'm looking for, clone it
                st[clone].len = st[p].len + 1;
                st[clone].next = st[q].next;
                st[clone].link = st[q].link;
                while (p != -1 && st[p].next[c] == q){
                    st[p].next[c] = clone;
                    p = st[p].link;
                }
                st[q].link = st[cur].link = clone;
            }
        }
        prev = cur;
    }
    // To check for occurrence of substring or largest prefix, just follow transitions.
    ll get_distinct(){ // Returns the number of distinct substrings in our automaton
        ll tot = 0;
        for (int i = 1; i < sz; ++i){
            tot += st[i].len - st[st[i].link].len;  // We just do this and avoid double counting
        }
        return tot;
    }
    ll tot_len_distinct(){
        ll tot = 0;
        for (int i = 0; i < sz; ++i){
            ll shortest = st[st[i].link].len + 1;   // Each node has the substrings of
            ll longest = st[i].len;                 // length shortest to longest.
            ll num_strings = longest - shortest + 1;
            ll cur = num_strings * (longest - shortest) / 2; // sum of arithmetic prog
            tot += cur;
        }
        return tot;
    }
    suffix_automaton(){
        sa_init();
    }
};

class Compare { // A custom compare function that you can modify and toss into set, pq, etc.
    public:
        bool operator()(pii x, pii y){
            auto [a, b] = x;
            auto [c, d] = y;
            return (a / 2) * b > (c / 2) * d;
        }
};

struct bridge_finding{
    vvi AL{};
    int tin[F];
    int low[F];
    bool vis[F];
    int tim = 0;
    void dfs(int u, int p){
        vis[u] = true;
        tin[u] = tim;
        low[u] = tim;
        ++tim;
        for (int v: AL[u]){
            if (v == p) continue;
            if (vis[v]) {
                low[u] = min(low[u], tin[v]);
                continue;
            }
            dfs(v, u);
            low[u] = min(low[u], low[v]);
            if (low[v] > tin[u]) {
                printf("found a brige\n");
            }
        }
    }
};

struct lyndon_factorization {
    vector<string> lf{};
    vi inds{};
    void factorization(string &s){
        int n;
        // s.size();
        int i = 0;
        while (i < n){
            int j = i + 1;
            int k = i;
            while (j < n && s[k] <= s[j]){
                if (s[k] < s[j]) k = i;
                else ++k;
                ++j;
            }
            while (i <= k) {
                lf.push_back(s.substr(i, j - k));
                inds.push_back(i);
                i += j - k;
            }
        }
    }
    string min_cyc(string &s){
        int n = s.size();
        string ss = s + s;
        factorization(ss);
        for (int i = 0; i < (int)inds.size() - 1; ++i){
            if (inds[i] < n && inds[i + 1] >= n) return lf[i];
        }
        return "";
    }
};

struct suffix_array{
    const char* T;
    int n;
    vi RA;
    vi SA;
    vi LCP;
    int alpha_size = 256; // Might be smaller
    void countingSort(int k){ // This is to be used on the rank array RA
        vi c(max(n, alpha_size), 0);
        for (int i = 0; i < n; ++i){
            ++c[i + k < n ? RA[i + k] : 0]; // count frequency of each item
        }
        for (int i = 1; i < alpha_size; ++i){ // Now make cumulative freq.
            c[i] += c[i - 1];
        }
        vi tempSA(n);
        for (int i = 0; i < n; ++i){ // sorts tempSA. For each 
            tempSA[c[SA[i] + k < n ? RA[SA[i] + k] : 0]++] = SA[i];
        }
        swap(SA, tempSA);
    }

    void construct(){
        SA.resize(n);
        iota(SA.begin(), SA.end(), 0);
        RA.resize(n);
        for (int i = 0; i < n; ++i) RA[i] = T[i]; // initial ranking is the character
        for (int k = 1; k < n; k <<= 1){
            countingSort(k);
            countingSort(0);
            vi tempRA(n); // Now we update the rankings of SA, after sorting SA by radix sort
            int r = 0;
            tempRA[SA[0]] = r;
            for (int i = 1; i < n; ++i){
                if ((RA[SA[i]] == RA[SA[i-1]]) && (RA[SA[i]+k] == RA[SA[i-1]+k])) tempRA[SA[i]] = r; 
                else tempRA[SA[i]] = ++r; // compare adj suffixes, same pair => same rank r; otherwise, increase r
            }
            swap(RA, tempRA);
            if (RA[SA[n-1]] == n - 1) break; // This means no ties, so we are done
        }
    }
    suffix_array(char *Tstring, int _n){
        n = _n;
        T = Tstring;
        construct();
    }
    void LCPr(){ // Returns an array that is the longest common prefix of adjacent elements
        vi phi(n); // I'm not sure permuting and repermuting is necessary, but whatever
        vi plcp(n);
        phi[SA[0]] = -1;
        for (int i = 0; i < n; ++i){
            phi[SA[i]] = SA[i - 1];
        }
        int L = 0;
        for (int i = 0; i < n; ++i){
            if (phi[i]== -1){plcp[i] = 0; continue;}
            while (i + L < n && phi[i] + L < n && T[i + L] == T[phi[i] + L]){ // prefix of consecutive elements
                ++L;
            }
            plcp[i] = L;
            if (L > 0) --L;
        }
        LCP.resize(n);
        for (int i = 0; i < n; ++i) LCP[i] = plcp[SA[i]];
        // for LCP of arbitrary inds i, j, do RMQ(LCP, i, j);
    }
    void print_sfx(){
        for (int i = 0; i < n; ++i){
            for (int j = SA[i]; j < n; ++j){
                printf("%c", T[j]);
            }
            printf("\n");
        }
    }
};

void sfx_array(){
    string s;
    int inds[30000];
    cin >> s; int n = s.length();
    iota(inds, inds+n, 0);
    vpi pair_rank{};
    pair_rank.assign(n, {});
    int r[n];

    for (auto k : {1, 2, 4, 8}){
        int v = 0;
        for (int i = 0; i < n; ++i){
            if (k == 1) {r[i] = s[i]; continue;}
            if (r[inds[i]] == r[inds[i - 1]]) r[inds[i]] = v;
            else {r[inds[i]] = v + 1; ++v;}
        }

        for (int i = 0; i < n; ++i){
            if (i + k >= n) {
                pair_rank[i] = {s[i], -1};
            } else {
                pair_rank[i] = {s[i], s[i + k]};
            }
        }
        sort(inds, inds + n, [pair_rank](int a, int b){ return pair_rank[a] < pair_rank[b]; });
    }
   
    // print_sfx();
}

struct lis{ // find and return longest increasing subsequence, use inner portion only O(nlogn)
    int a[501];
    int pre[501];
    map<int, int> indof{};
    bool in[501]{};
    void get_lis(){
        memset(in, false, sizeof(in));
        indof.clear();
        int n; scanf("%d", &n);
        for (int i = 0; i < n; ++i){
            scanf("%d", a + i);
            indof[a[i]] = i;
        }
        vi lis{a[0]};
        pre[0] = -1;
        for (int i = 1; i < n; ++i){
        auto ind = lower_bound(lis.begin(), lis.end(), a[i]) - lis.begin();
        if (ind == lis.size()) {lis.push_back(a[i]); pre[i] = indof[lis[ind - 1]];}
        else {
            if (ind == 0) pre[i] = -1;
            else pre[i] = indof[lis[ind - 1]];
            lis[ind] = a[i];
        }
    }
        int cur = indof[lis[lis.size() - 1]];
        while (cur != -1){
            in[cur] = true;
            cur = pre[cur];
        }
    }
};
struct trie{ // Constructs a fastish lookup for strings in O(m * k) time, where m is sum of all strings and k is len(alphabet)
    // Now updated with Aho Corasick algorithm
    struct vertex{
        int next[26];
        bool word = false;
        int p = -1; // The parent of this node
        char pch; // the character that got us here.
        int link = -1; // The suffix link
        vertex(int par = -1){
            pch = '#';
            p = par;
            link = -1;
            memset(next, -1, sizeof(next));
            word = false;
        }
    };

    vector<vertex> t{vertex()};
    void addstring(string &s){
        int v = 0;
        for (char ch : s){
            int &cind = t[v].next[ch - 'a'];
            if (cind == -1){
                cind = t.size();
                t.push_back(vertex(v));
            }
            v = cind;
        }
        t[v].word = true;
    }

    bool search(string &s){
        int v = 0;
        for (char ch: s){
            int cind = t[v].next[ch - 'a'];
            if (cind == -1) return false;
            v = cind;
        }
        return t[v].word;
    }

    int get_link(int v){ // Given an index v, find the index of the longest proper suffix of v in the tree, if it exists
        if (t[v].link != -1) return t[v].link;
        int &ret = t[v].link;
        
        if (v == 0 || t[v].p == 0) {ret = 0; return 0;}
        int vp = t[v].p;
        int vp_child = t[vp].next[t[v].pch - 'a'];
        if (vp_child == -1){
            int root_child = t[0].next[t[v].pch - 'a'];
            if (root_child == -1) ret = 0;
            else ret = root_child;
        } else {
            ret = vp_child;
        }
        return ret;
    }
};

struct manacher{ // Find d, where d[i] is the number of palindromes centered at i, in O(n) time
    
    vi findp(string &s){ // This only finds odd length palindromes
        int n = s.length();
        vi d(n + 2, 0);
        s = '$' + s + '@';
        int l = 0;
        int r = 0;
        for (int i = 1; i <= n; ++i){
            d[i] = max(0, min(r - i, d[l + r - i]));
            while (s[d[i] + i] == s[i - d[i]]) ++d[i];
            if (i + d[i] > r) l = i - d[i]; r = i + d[i];
        }
        vi ans(d.begin() + 1, d.end() - 1);
        return ans; // pass reference if this is slow
    }

    string preprocess(string &s){ // since it only finds odd length palindromes
        string t = "";
        t += s[0];
        for (int i = 1; i < s.size(); ++i){
            t += "#" + s[i];
        }
        return t;
    }
};
// Generic Print Array
void printarr(int *a, int asize){
    for(int i = 0; i < asize; ++i){
        printf("%d ", *a);
        ++a;
    }
    printf("\n");
}

// Mergesort
ll merge(ll arr[], int left, int mid, int right) {
    int i = left, j = mid, k = 0;
    ll invCount = 0;
    int temp[(right - left + 1)];

    while ((i < mid) && (j <= right)) {
        if (arr[i] <= arr[j]) {
            temp[k] = arr[i];
            ++k; ++i;
        } else {
            temp[k] = arr[j];
            invCount += (mid - i);
            ++k; ++j;
        }
    }

    while (i < mid) {
        temp[k] = arr[i];
        ++k; ++i;
    }

    while (j <= right) {
        temp[k] = arr[j];
        ++k; ++j;
    }

    for (i = left, k = 0; i <= right; i++, k++) {
        arr[i] = temp[k];
    }

    return invCount;
}
ll mergeSort(ll arr[], int left, int right) {
  ll invCount = 0;
 
  if (right > left) {
    int mid = (right + left) / 2;
    invCount = mergeSort(arr, left, mid);
    invCount += mergeSort(arr, mid + 1, right);
    invCount += merge(arr, left, mid + 1, right);
  }
  return invCount;
}

struct ternary_search { // Find the peak of an array or function that goes up then down
    ll s; ll k;
    ll func(ll x){ // replace with your function or lookup array
        int disc = 20 * (x / 4) + s;
        x = x % 4;
        while (--x){
            disc += disc % 10;
        }
        return disc * (k - x);
    }
    int tsearch(int l, int r){
        if (l == r) return func(l);
        if (r < l + 3) return max(func(l + 2), (max(func(l), func(l + 1))));
        int m1 = l + (r - l) / 3;
        int m2 = r - (r - l) / 3;
        if (func(m1) < func(m2)){
            return tsearch(m1, r);
        } else if (func(m1) > func(m2)) {
            return tsearch(l, m2);
        } else {
            return tsearch(m1, m2);
        }
    }
};
// Fenwick Tree: Can answer Range Sum Query, Cumulative frequency (CDF) 
// on actively manipulated and queried data. Assumes all elements are in
// the range 1...m
// FT is indexed by 1...m (no zero)
struct fenwick_tree {
    vi ft;
    fenwick_tree(int m){ft.assign(m + 1, 0);}
    // Returns the sum of values 1 ... j
    int rsq(int j){
        int sum = 0;
        for (; j > 0; j -= lso(j)){
            sum += ft[j];
        }
        return sum;
    }
    void update(int i, int v){
        for (; i > 0; i += lso(i)){
            ft[i] += v;
        }
    }
    void range_update(int i, int j, int v){
        ft[i] += v; 
        if (j + 1 < ft.size()) ft[j + 1] -= v;
    }
};

struct RQRU {
    fenwick_tree fwt1 = fenwick_tree(F);
    fenwick_tree fwt2 = fenwick_tree(F);
    void range_update(int l, int r, int x){
        fwt1.update(l, x);
        fwt1.update(r, -x);
        fwt2.update(l, x * (l - 1));
        fwt2.update(r + 1, -x * r);
    }
    int prefix_sum(int idx){
        return fwt1.rsq(idx) * idx - fwt2.rsq(idx);
    }
};

// Dinic's Algorithm: Does not handle multiedges well, so consider condensing edges first.
struct Dinic {
    struct flowedge{
        int u; int v; ll cap; ll flow;
        flowedge(int _u, int _v, int _cap, int _flow){
            u = _u; v = _v; cap = _cap; flow = _flow;
        }
    };
    vvi AL{};
    vvi ptr{};
    bool vis[F/10]{};
    // set s, t to correct values
    int s = 0;
    int t = F / 10;
    vector<flowedge> edges{};

    void init(int n){
        AL.assign(n, vi());
        ptr.assign(n, vi());
        memset(vis, false, sizeof(vis));
        // Still initialize target
    }
    void add_e(int u, int v, int cap){
        edges.push_back({u, v, cap, 0});
        edges.push_back({v, u, 0, 0});
        AL[u].push_back(edges.size() - 2);
        AL[v].push_back(edges.size() - 1);
    }

    bool bfs(int s){
        qi nodes{}; nodes.push(s);
        vis[s] = true;
        while(!nodes.empty()){
            int u = nodes.front(); nodes.pop();
            vis[u] = true;
            for (auto id : AL[u]){
                auto &e = edges[id];
                if (vis[e.v]) continue;
                if (e.cap - e.flow < 1) continue;
                nodes.push(e.v);
                ptr[e.u].push_back(id);
            }
        }
        return vis[t];
    }

    ll dfs(int u, ll pushed){
        if (pushed == 0) return 0;
        if (u == t) return pushed;
        for (auto id: ptr[u]){
            auto &e = edges[id];
            if (!vis[e.v] || e.cap - e.flow < 1) continue;
            ll tr = dfs(e.v, min(pushed, e.cap - e.flow));
            if (tr == 0) continue;
            e.flow += tr;
            edges[id ^ 1].flow -= tr;
            return tr;
        }
        return 0ll;
    }

    ll runner(){
        ll tot = 0;
        int itc = 0;
        while (true){
            memset(vis, false, sizeof(vis));
            ptr.clear();
            ptr.assign(AL.size(), vi());
            if (!bfs(s)) break;
            ll pushed = 1;
            while (pushed > 0) {
                tot += pushed;
                pushed = dfs(s, INF);
            }
            tot -= 1;
        }

        for (auto &v: ptr){
            for (auto id: v){
                auto e = edges[id];
                printf("%d %d %lld %lld\n", e.u, e.v, e.cap, e.flow);
                e = edges[id ^ 1];
                printf("%d %d %lld %lld\n", e.u, e.v, e.cap, e.flow);
            }
        }
        printf("\n\n");

        return tot;
    }
};

struct MCMF{
    struct flowedge{
        int u, v, cap, cost;
        flowedge(int _u, int _v, int _cap, int _cost){
            u = _u; v = _v; cap = _cap; cost = _cost;
        }
    };
    map<pii, int> cost{};
    map<pii, int> cap{};
    // const int ssz = 2004;
    // ll cost[ssz][ssz]{}; // This runs in O(F*n^3) or maybe a little better
    // ll cap[ssz][ssz]{};  // Set these to n limit. If runtime error use map
    vvi AL{};
    vector<flowedge> edges{};
    void spfa(int n, int u0, vi &d, vi &p){ // find shortest path. Populate d with distances and p with parents. Runs in O(mn), but average case better
        d.assign(n, MOD);
        d[u0] = 0;
        bool inq[n]; memset(inq, false, sizeof(inq));
        qi q{};
        q.push(u0); inq[u0] = true;
        p.assign(n, -1);
        while (q.size()){
            int u = q.front(); q.pop();
            inq[u] = false;
            for (int v: AL[u]){
                if (cap[{u , v}] > 0 && d[v] > d[u] + cost[{u , v}]){
                    d[v] = cost[{u , v}] + d[u];
                    p[v] = u;
                    if (!inq[v]){
                        inq[v] = true;
                        q.push(v);
                    }
                }
            }
        }
    }
    pii min_cost_flow(int n, vector<flowedge>& edges, int K, int s, int t){ // K is the flow we need. Can set K to INF for Min cost max flow
        AL.assign(n, vi());
        for (flowedge e: edges){
            AL[e.u].push_back(e.v);
            AL[e.v].push_back(e.u);
            cost[{e.u , e.v}] = e.cost;
            cost[{e.v , e.u}] = -e.cost;
            cap[{e.u , e.v}] = e.cap;
        }
        int fl = 0; int cost = 0;
        vi d, p;
        while (fl < K){ // Can set K to INF still, no worries
            spfa(n, s, d, p);
            if (d[t] == MOD) break;

            int f = K - fl; int cur = t;
            while (cur != s){ // we have a path, find the min capacity on that path
                f = min(f, cap[{p[cur], cur}]);
                cur = p[cur];
            }

            fl += f; cost += f * d[t]; // d is dist but actually cost
            cur = t;
            while (cur != s){ // now we apply the flow
                cap[{p[cur] , cur}] -= f;
                cap[{cur , p[cur]}] += f;
                cur = p[cur];
            }
        }
        return {fl, cost}; // can also return other stuff
    }
};
// log base 2 of an integer (ignore error it works fine)
// int lg(ul x){return bit_width(x) - 1;}

struct mcbm { // the maximum cardinality bipartite matching. Use the inner portion, not as a struct
    vvi AL{};
    bool col[500];
    int n, s, t; // the number of total, blue, red verticies in the bipartite graph
    vi mt; // the blue vertex that corresponds to each red vertex
    bool vis[500]; // Runs in O(n*m) 
    bool used[500];

    bool try_kuhn(int v) { // DFS that searches for augmenting paths and flips those that it finds.
        if (used[v]) return false;
        used[v] = true;
        for (int to : AL[v]) {
            if (mt[to] == -1 || try_kuhn(mt[to])) {
                mt[to] = v;
                return true;
            }
        }
        return false;
    }
    
    void print_mcbm(){
        mt.assign(s, -1);
        memset(vis, false, sizeof(vis));
        for (int i = 0; i < n; ++i){ // A heuristic, which speeds up the algo on random graphs
            if (col[i]) continue; // if at blue, continue
            for (int v: AL[i]){
                if (mt[i] == -1 && !vis[v]) {
                    mt[i] = v;
                    vis[v] = true;
                    break;
                }
            }
        }
        for (int i = 0; i < n; ++i){
            if (vis[i]) continue;
            memset(used, false, sizeof(used));
            try_kuhn(i);
        }
        for (int i = 0; i < n; ++i){
            if (mt[i] != -1) printf("%d %d\n", mt[i] + 1, i + 1);
        }
    }
};
// Sparse_Table implementation with min queries
struct Sparse_Table { // Should be l, r inclusive
    int st[20][F];
    void initialize(int a[], int n){
        for (int i = 0; i < n; ++i){
            st[0][i] = a[i];
        }
        for (int i = 1; i < 20; ++i){
            for (int j = 0; j < n; ++j){
                if (j + (1 << i) < n){
                    st[i][j] = min(st[i - 1][j], st[i - 1][j + (1 << (i - 1))]);
                }
            }
        }
    }
    int lg(ul x){
        return bit_width(x) - 1;
    }
    int query(int l, int r){
        if (r < l) return 0;
        int i = lg(r - l + 1);
        return min(st[i][l], st[i][r - (1 << i) + 1]);
    }
};

//TREAP, implemented with max heap. Keeps a binary search tree of key, max heap of value
struct tnode {
    int key, priority;
    tnode *tl, *tr;
    tnode () { }
    // tnode (int key) : key(key), prior(rand()), l(NULL), r(NULL) { }
    tnode (int key, int priority) : key(key), priority(priority), tl(NULL), tr(NULL) { }
};

void split (tnode* t, int key, tnode* & l, tnode* & r) {
    if (!t)
        l = r = NULL;
    else if (t->key <= key)
        split (t->tr, key, t->tr, r),  l = t;
    else
        split (t->tl, key, l, t->tl),  r = t;
}

void insert (tnode* & t, tnode* it) {
    if (!t)
        t = it;
    else if (it->priority > t->priority)
        split (t, it->key, it->tl, it->tr),  t = it;
    else
        insert (t->key <= it->key ? t->tr : t->tl, it);
}

void merge (tnode* & t, tnode* l, tnode* r) {
    if (!l || !r)
        t = l ? l : r;
    else if (l->priority > r->priority)
        merge (l->tr, l->tr, r),  t = l;
    else
        merge (r->tl, l, r->tl),  t = r;
}

void erase (tnode* & t, int key) {
    if (t->key == key) {
        tnode* th = t;
        merge (t, t->tl, t->tr);
        delete th;
    }
    else
        erase (key < t->key ? t->tl : t->tr, key);
}

tnode* unite (tnode* l, tnode* r) {
    if (!l || !r)  return l ? l : r;
    if (l->priority < r->priority)  swap (l, r);
    tnode* lt; tnode* rt;
    split (r, l->key, lt, rt);
    l->tl = unite(l->tl, lt);
    l->tr = unite(l->tr, rt);
    return l;
}

struct union_find { // onion find lol
    int par[2 * F + 1]{};

    int find(int x){
        if (x == par[x]) return x;
        int ret = find(par[x]);
        par[x] = ret;
        return ret;
    }

    void onion(int x, int y){
        int px = find(x);
        int py = find(y);
        par[px] = py;
    }
};
vector<string> split(string s, char sep){
    stringstream ss(s);
    string word;
    vector<string> ans{};
    while (!ss.eof()) {
        getline(ss, word, sep);
        ans.push_back(word);
    }
    return ans;
}

// Segment tree, currently setup for RSQ
struct Tree { // be sure to CHANGE UNIT
    typedef ll T; // The type of the tree elements eg int, ll, etc.
    static constexpr T unit = 0; // the default value of node, for RSQ = 0, for RMinQ +INF, for RMaxQ -INF
    T f(T a, T b) { return (a + b); } // (any associative fn) eg. sum, min, max
    vector<T> s; // tree nodes
    int n; // size of array
    Tree(int n = F, T def = unit) : s(2*n, def), n(n) {} // pass in array size, default value
    void update(int pos, T val) {
        pos += n; // the node corresponding to only pos is at pos + n;
        for (s[pos] = val; pos /= 2;) // pos /= 2 takes us up to our parent node and checks that pos/2 > 0
            // equivalent to (...; pos/2; pos /= 2)
            s[pos] = f(s[pos * 2], s[pos * 2 + 1]); // the parent is function of children
    }
    T query(int b, int e) { // query [b, e) inclusive left, exclusive right
        T ra = unit, rb = unit; // the lower accumulation and upper accumulation are set to default
        b += n; e += n; // start with original b, e locations.
        for (; b < e; b /= 2, e /= 2) { // b/=2 and e/=2 push the bounds up the tree
            if (b % 2) ra = f(ra, s[b++]); // if b is odd, accumulate the answer at b, then make b even
            // we use post-inccrement because we're inclusive at lower bound, check value, then add
            if (e % 2) rb = f(s[--e], rb); // if e is odd, accumulate the answer at e, then make e even
            // we use pre-decrement because we're exclusive at upper bound, subtract first, then check value
        }
        return f(ra, rb); // combine the lower bound accumulation and upper bound accumulation.
    }
};
// Can solve range assignment point query.
struct lazy_segment_tree{
    int n; int st[4*F]{};
    bool marked[4 * F]{};
    lazy_segment_tree(int asize) {n = asize;}
    void build(int a[], int v, int tl, int tr){
        if (tl == tr) {st[v] = a[tl]; return;}
        int tm = (tl + tr) / 2;
        build(a, v, tl, tm);
        build(a, v, tm + 1, tr); 
    }
    void push(int v){
        st[2 * v] = st[v];
        st[2 * v + 1] = st[v];
        marked[2 * v + 1] = true;
        marked[2 * v] = true;
        marked[v] = false;
    }
    void assign(int v, int tl, int tr, int l, int r, int val){
        if (l > r) return;
        if (tl == l && tr == r){
            st[v] = val;
            marked[v] = true;
        } 
        if (marked[v]) push(v);
        int tm = (tl + tr) / 2;
        assign(2 * v, tl, tm, l, min(l, tm), val);
        assign(2 * v + 1, tm + 1, tr, max(tm + 1, l), r, val);
    }
    int query(int v, int tl, int tr, int pos){
        if (tl == tr) return st[v];
        if (marked[v]) push(v);
        int tm = (tl + tr) / 2;
        if (pos <= tm) return query(2 * v, tl, tm, pos);
        else return query(2 * v + 1, tm + 1, tr, pos);
    }
};

// gets the bit width of an int (can do long, char too ig).
int width(int x){
    for (int i = 31; i >= 0; --i){
        if (x & (1 << i)) return i;
    }
    return 0;
}


struct rolling_hash{ 
    string s;
    int n;
    ll p = 31;
    ll p2 = 41;
    vll pows{1, p};
    vll pows2{1, p2};
    ll hash[F];
    ll h[F];
    rolling_hash(){
        cin >> s;
        n = s.length();
        hash[0] = 0;
        for (int i = 0; i < n; ++i){
            hash[i + 1] = hash[i] + (pows[i] * (s[i] - 'a' + 1)) % MOD;
            hash[i + 1] %= MOD;
            pows.push_back((p * pows[i + 1]) % MOD);
        }
        h[0] = 0;
        for (int i = 0; i < n; ++i){
            h[i + 1] = h[i] + (pows2[i] * (s[i] - 'a' + 1)) % MOD;
            h[i + 1] %= MOD;
            pows2.push_back((p2 * pows2[i + 1]) % MOD);
        }
    }
    // Returns the hash value of a substring, [l, r), multiplied by some number pow[n - l] to check equality.
    pll stval(int l, int r){
        // printf("%d %d\n", l, r);
        return {(((hash[r] - hash[l] + MOD) % MOD) * pows[n - l]) % MOD, (((h[r] - h[l] + MOD) % MOD) * pows2[n - l]) % MOD};
    }
    void list_unique(){
        set<pll> seen{};
        for (int i = 0; i <= n; ++i){
            for (int j = i; j <= n; ++j){
                pll x = stval(i, j);
                if (seen.count(x)) continue;
                for (int y = i; y < j; ++y){
                    printf("%c", s[y]);
                } 
                printf(" {%lld %lld}\n", x.first, x.second);
                seen.insert(x);
            }
        }
    }
};

// Recursive function to return (x ^ n) % m
ll modexp(ll x, ll n) {
    if (n == 0) return 1;
    else if (n % 2 == 0)  return modexp((x * x) % MOD, n / 2);
    else return (x * modexp((x * x) % MOD, (n - 1) / 2) % MOD);
}
 
// fraction modulo a prime, (denom ^ (MOD - 2)) * numerator, all % MOD
ll frac_mod(ll a, ll b){
    ll c = gcd(a, b);
    a = a / c;
    b = b / c;
    // (b ^ m-2) % m
    ll d = modexp(b, MOD - 2);
    // Final answer
    ll ans = ((a % MOD) * (d % MOD)) % MOD;
    return ans;
}

struct factorial {
    const int MAXN = 5e6;
    vll fact{};
    vll inv{};

    ll extgcd(ll a, ll b, ll& x, ll& y){
        // compute g = gcd(a, b), and 
        // x, y s.t. ax + by = g
        if (b == 0){
            x = 1; y = 0;
            return a;
        }
        ll x1, y1;
        ll d = extgcd(b, a % b, x1, y1);
        x = y1;
        y = x1 - y1 * (a / b);
        return d;
    }
    ll modinv(ll val){
        ll x, y;
        extgcd(val, MOD, x, y);
        return x;
    }
    void invs() {
        inv.resize(MAXN + 1);
        ll v = 1;
        for (int i = 0; i < MAXN; ++i) {
            inv[i] = v;
            v = v * fact[i] % MOD;
        }
        ll x, y;
        extgcd(v, MOD, x, y);
        if (x < 0) x += MOD;
        for (int i = MAXN - 1; i >= 0; --i) {
            inv[i] = x * inv[i] % MOD;
            x = x * fact[i] % MOD;
        }
    }

    ll choose(ll n, ll r){
        ll ans = (((fact[n] * inv[r]) % MOD) * inv[n - r]) % MOD;
        return ans;
    }
    factorial(){
        fact.resize(MAXN + 1);
        fact[0] = 1;
        for (int i = 1; i <= MAXN; ++i){
            fact[i] = (fact[i - 1] * i) % MOD;
        }
        invs();
    }

};

struct catalan{ // Don't use as struct, just take inside part
    const int MaxN = 3 * F + 1;
    vll cat{1};

    void pre(){
        cat.reserve(MaxN);
        for (int i = 1; i <= MaxN; ++i){
            ll ncat = 2 * (2 * i + 1) * cat[i - 1];
            ncat %= MOD;
            ncat *= modexp(i + 2, MOD - 2);
            ncat %= MOD;
            cat.push_back(ncat);
        }
    }
};
// DP, sum over subsets
// Given an array A of length 2^n, we need for all x, the sum of A[i] if x & i = i
void sos(int arr[], int n){
    // dp[mask][i] is the set of subsets of mask that differ only in the first i bits
    ll dp[(1 << n)][n + 1];
    for (int mask = 0; mask < (1 << n); ++mask){
        dp[mask][0] = arr[mask];
        for (int i = 1; i <= n; ++i){
            dp[mask][i] = dp[mask][i - 1];
            if (mask & (1 << i)) dp[mask][i] += dp[mask ^ (1 << i)][i - 1];
        }
    }
    // Our answers lie in dp[mask][n - 1] for all masks
}

// void ordered_set_usage(){
//     os(int) s;
//     s.insert(4);
//     s.insert(7);
//     printf("Order of %d\n", s.order_of_key(5));
//     printf("Find by order %d\n", s.find_by_order(2));
//     printf("%d\n", s.find(4));
//     for (auto x : s){
//         printf("%d ", x);
//     }
// }
// When dp[i, j] = min_k {dp[i][k] + dp[k + 1][j] + C(i, j)}
void knuth(int arr[], int n){
    int dp[n][n]; int opt[n][n];
    // Example cost fn. Must satisfy C(a, d) + C(b, c) >= C(a, c) + C(b, d) and C(a, d) >= C(b, c)
    auto C = [&](int x, int y){return y - x;};
    // Initialize dp[i][i] correctly
    for (int i = 0; i < n; ++i){
        opt[i][i] = i;
        dp[i][i] = 0;
    }
    for (int i = n - 2; i >= 0; --i){
        for (int j = i + 1; j < n; ++j){
            int mn = MOD;
            int cost = C(i, j);
            for (int k = opt[i][j - 1]; k < min(j - 1, opt[i + 1][j]); ++k){
                if (mn >= dp[i][k] + dp[k+1][j] + cost){
                    opt[i][j] = k;
                    mn = dp[i][k] + dp[k+1][j] + cost;
                }
            }
            dp[i][j] = mn;
        }
    }
    printf("%d\n", dp[0][n-1]);
}

auto cmp = [](pii a, pii b){
    if (a.first == b.first) return a.second > b.second;
    return a.first < b.first;
};
set<pii, decltype(cmp)> s; // a set with custom cmp


const int inf = 1e9;
struct Node {
	Node *l = 0, *r = 0;
	ll lo, hi, mset = 0, madd = 0, val = 0;
	Node(ll lo,ll hi):lo(lo),hi(hi){} // Large interval of -inf
	Node(vi& v, ll lo, ll hi) : lo(lo), hi(hi) {
		if (lo + 1 < hi) {
			ll mid = lo + (hi - lo)/2;
			l = new Node(v, lo, mid); r = new Node(v, mid, hi);
			val = (l->val + r->val);
		}
		else val = v[lo];
	}
	ll query(ll L, ll R) {
		if (R <= lo || hi <= L) return -inf;
		if (L <= lo && hi <= R) return val;
		push();
		return (l->query(L, R) + r->query(L, R));
	}
	void set(ll L, ll R, ll x) {
		if (R <= lo || hi <= L) return;
		if (L <= lo && hi <= R) mset = val = x, madd = 0;
		else {
			push(), l->set(L, R, x), r->set(L, R, x);
			val = (l->val + r->val);
		}
	}
	void add(ll L, ll R, ll x) {
		if (R <= lo || hi <= L) return;
		if (L <= lo && hi <= R) {
			if (mset != inf) mset += x;
			else madd += x;
			val += x;
		}
		else {
			push(), l->add(L, R, x), r->add(L, R, x);
			val = (l->val + r->val);
		}
	}
	void push() {
		if (!l) {
			ll mid = lo + (hi - lo)/2;
			l = new Node(lo, mid); r = new Node(mid, hi);
		}
		if (mset != inf)
			l->set(lo,hi,mset), r->set(lo,hi,mset), mset = inf;
		else if (madd)
			l->add(lo,hi,madd), r->add(lo,hi,madd), madd = 0;
	}
};

int main(){
}

// g++ -o helper helper.cpp -fsanitize=undefined -std=c++20