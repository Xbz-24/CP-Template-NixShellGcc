  #ifndef _GLIBCXX_NO_ASSERT
  #include <cassert>
  #endif
  #include <cctype>
  #include <cerrno>
  #include <cfloat>
  #include <ciso646>
  #include <climits>
  #include <clocale>
  #include <cmath>
  #include <csetjmp>
  #include <csignal>
  #include <cstdarg>
  #include <cstddef>
  #include <cstdio>
  #include <cstdlib>
  #include <cstring>
  #include <ctime>
  #if __cplusplus >= 201103L
  #include <ccomplex>
  #include <cfenv>
  #include <cinttypes>
  #include <cstdbool>
  #include <cstdint>
  #include <ctgmath>
  #include <cwchar>
  #include <cwctype>
  #include <exception>
  #include <stdexcept>
  #endif
  #include <algorithm>
  #include <bitset>
  #include <complex>
  #include <deque>
  #include <exception>
  #include <fstream>
  #include <functional>
  #include <iomanip>
  #include <ios>
  #include <iosfwd>
  #include <iostream>
  #include <istream>
  #include <iterator>
  #include <limits>
  #include <list>
  #include <locale>
  #include <map>
  #include <memory>
  #include <new>
  #include <numeric>
  #include <ostream>
  #include <queue>
  #include <set>
  #include <sstream>
  #include <stack>
  #include <stdexcept>
  #include <streambuf>
  #include <string>
  #include <typeinfo>
  #include <utility>
  #include <valarray>
  #include <vector>
  #if __cplusplus >= 201103L
  #include <array>
  #include <atomic>
  #include <chrono>
  #include <condition_variable>
  #include <forward_list>
  #include <future>
  #include <initializer_list>
  #include <mutex>
  #include <random>
  #include <ratio>
  #include <regex>
  #include <scoped_allocator>
  #include <system_error>
  #include <thread>
  #include <tuple>
  #include <typeindex>
  #include <type_traits>
  #include <unordered_map>
  #include <unordered_set>
  #include <ext/pb_ds/assoc_container.hpp>
  #include <ext/pb_ds/tree_policy.hpp>
  #include <ext/pb_ds/hash_policy.hpp>
  #include <ext/pb_ds/trie_policy.hpp> 
  #include <ext/pb_ds/priority_queue.hpp>
  #endif
using namespace std;
#define ll long long
#define ld long double
#define ull unsigned long long
#define pb push_back
#define mp make_pair
#define F first
#define S second
#define ALL(x) (x).begin(), (x).end()
#define sz(x) (int)(x).size()


template<typename T> void _dbg(const char* _s, T _h) { cerr << _s << " = " << _h << "\n"; }
template<typename T, typename... Ts> void _dbg(const char* _s, T _h, Ts... _t){
    int _b = 0;
    while (*_s != ',' || _b != 0) {
        if (*_s == '(' || *_s == '{' || *_s == '[') _b++;
        if (*_s == ')' || *_s == '}' || *_s == ']') _b--;
        cerr << *_s++;
    }
    cerr << " = " << _h << ",";
    _dbg(_s + 1, _t...);
}
#define dbg(...) _dbg(#__VA_ARGS__, __VA_ARGS__)
void setIO(string s = "") {
    std::ios_base::sync_with_stdio(false);
    std::cin.tie(NULL);
    if (!s.empty()) {
        freopen((s + ".in").c_str(), "r", stdin);
        freopen((s + ".out").c_str(), "w", stdout);
    }
}
ll binpow(ll a, ll b) {
    ll res = 1;
    while (b > 0) {
        if (b & 1) res *= a;
        a *= a;
        b >>= 1;
    }
    return res;
}
ll modpow(ll a, ll b, ll mod) {
    ll res = 1;
    a %= mod;
    while (b > 0) {
        if (b & 1) res = res * a % mod;
        a = a * a % mod;
        b >>= 1;
    }
    return res;
}
bool isPrime(ll n) {
    if (n <= 1) return false;
    for (ll i = 2; i * i <= n; ++i)
        if (n % i == 0) return false;
    return true;
}
vector<bool> sieve(int n) {
    vector<bool> prime(n+1, true);
    prime[0] = prime[1] = false;
    for (int p = 2; p*p <= n; p++) {
        if (prime[p]) {
            for (int i = p*p; i <= n; i += p) {
                prime[i] = false;
            }
        }
    }
    return prime;
}
template<class T> struct segtree {
    int n; vector<T> tree;
    void build(int k, int l, int r, const vector<T>& v) {
        if (l == r) {
            if (l < sz(v)) tree[k] = v[l];
            return;
        }
        int mid = (l + r) / 2;
        build(2*k, l, mid, v);
        build(2*k+1, mid+1, r, v);
        tree[k] = tree[2*k] + tree[2*k+1];
    }
    segtree(const vector<T>& v = {}) {
        n = sz(v);
        tree.assign(4*n, 0);
        build(1, 0, n-1, v);
    }
};
pair<ll, ll> extendedGCD(ll a, ll b) {
    if (b == 0)
        return {1, 0};
    auto [x1, y1] = extendedGCD(b, a % b);
    ll x = y1;
    ll y = x1 - (a / b) * y1;
    return {x, y};
}
template<typename T>
struct FenwickTree {
    vector<T> bit; 
    int n;
    FenwickTree(int n) {
        this->n = n;
        bit.assign(n + 1, 0);
    }
    T sum(int r) {
        T ret = 0;
        for (; r >= 1; r -= r & -r)
            ret += bit[r];
        return ret;
    }
    void add(int idx, T delta) {
        for (; idx <= n; idx += idx & -idx)
            bit[idx] += delta;
    }
    T sum(int l, int r) {
        return sum(r) - sum(l - 1);
    }
};
vector<int> kmp(string s) {
    int n = (int)s.length();
    vector<int> pi(n, 0);
    for (int i = 1; i < n; i++) {
        int j = pi[i-1];
        while (j > 0 && s[i] != s[j])
            j = pi[j-1];
        if (s[i] == s[j])
            j++;
        pi[i] = j;
    }
    return pi;
}
vector<ll> dijkstra(int s, vector<vector<pair<int, int>>>& adj) {
    int n = adj.size();
    const ll INF = 1e18;
    vector<ll> dist(n, INF);
    priority_queue<pair<ll, int>, vector<pair<ll, int>>, greater<pair<ll, int>>> pq;
    dist[s] = 0;
    pq.push({0, s});
    while (!pq.empty()) {
        auto [d, v] = pq.top();
        pq.pop();
        if (d != dist[v]) continue;
        for (auto edge : adj[v]) {
            int to = edge.first;
            int len = edge.second;
            if (dist[v] + len < dist[to]) {
                dist[to] = dist[v] + len;
                pq.push({dist[to], to});
            }
        }
    }
    return dist;
}
vector<ll> bellmanFord(int V, int E, int src, vector<tuple<int, int, int>>& edges) {
    vector<ll> dist(V, LLONG_MAX);
    dist[src] = 0;
    for (int i = 1; i <= V - 1; i++) {
        for (auto& e : edges) {
            int u, v, w;
            tie(u, v, w) = e;
            if (dist[u] != LLONG_MAX && dist[u] + w < dist[v]) {
                dist[v] = dist[u] + w;
            }
        }
    }
    return dist;
}
void floydWarshall(vector<vector<ll>>& dist) {
    int V = dist.size();
    for (int k = 0; k < V; k++) {
        for (int i = 0; i < V; i++) {
            for (int j = 0; j < V; j++) {
                if (dist[i][k] < LLONG_MAX && dist[k][j] < LLONG_MAX)
                    dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]);
            }
        }
    }
}
class LCA {
    int N, LOG;
    vector<int> depth;
    vector<vector<int>> up;
public:
    LCA(const vector<vector<int>>& adj, int root = 0) {
        N = adj.size();
        LOG = 32 - __builtin_clz(N);
        depth = vector<int>(N);
        up = vector<vector<int>>(N, vector<int>(LOG));
        dfs(root, root, adj);
    }
    void dfs(int u, int p, const vector<vector<int>>& adj) {
        up[u][0] = p;
        for (int i = 1; i < LOG; ++i)
            up[u][i] = up[up[u][i-1]][i-1];
        for (int v : adj[u]) {
            if (v == p) continue;
            depth[v] = depth[u] + 1;
            dfs(v, u, adj);
        }
    }
    int query(int u, int v) {
        if (depth[u] < depth[v]) swap(u, v);
        int diff = depth[u] - depth[v];
        for (int i = 0; i < LOG; ++i) {
            if (diff & (1 << i)) {
                u = up[u][i];
            }
        }
        if (u == v) return u;
        for (int i = LOG-1; i >= 0; --i) {
            if (up[u][i] != up[v][i]) {
                u = up[u][i];
                v = up[v][i];
            }
        }
        return up[u][0];
    }
};
vector<int> tarjanSCC(const vector<vector<int>>& graph) {
    int n = graph.size(), time = 0;
    vector<int> ids(n, -1), low(n), onStack(n);
    stack<int> st;
    vector<vector<int>> scc;
    function<void(int)> dfs = [&](int at) {
        st.push(at);
        onStack[at] = true;
        ids[at] = low[at] = time++;
        for (int to : graph[at]) {
            if (ids[to] == -1) dfs(to);
            if (onStack[to]) low[at] = min(low[at], low[to]);
        }
        if (ids[at] == low[at]) {
            vector<int> component;
            for (int node = -1; node != at;) {
                node = st.top(); st.pop();
                onStack[node] = false;
                component.push_back(node);
            }
            scc.push_back(component);
        }
    };
    for (int i = 0; i < n; ++i) if (ids[i] == -1) dfs(i);
    return vector<int>(scc.size());
}
class Dinic {
    struct Edge {
        int to, rev;
        ll cap, flow;
        Edge(int to, int rev, ll cap) : to(to), rev(rev), cap(cap), flow(0) {}
    };
    vector<vector<Edge>> graph;
    vector<int> level, ptr;
    int n, s, t;
    bool bfs() {
        queue<int> q({s});
        fill(level.begin(), level.end(), -1);
        level[s] = 0;
        while (!q.empty() && level[t] == -1) {
            int v = q.front(); q.pop();
            for (auto& e : graph[v]) {
                if (level[e.to] == -1 && e.flow < e.cap) {
                    q.push(e.to);
                    level[e.to] = level[v] + 1;
                }
            }
        }
        return level[t] != -1;
    }
    ll dfs(int v, ll pushed) {
        if (pushed == 0) return 0;
        if (v == t) return pushed;
        for (int& cid = ptr[v]; cid < (int)graph[v].size(); cid++) {
            Edge& e = graph[v][cid];
            Edge& rev = graph[e.to][e.rev];
            if (level[v] + 1 != level[e.to] || e.flow >= e.cap) continue;
            ll tr = dfs(e.to, min(pushed, e.cap - e.flow));
            if (tr == 0) continue;
            e.flow += tr;
            rev.flow -= tr;
            return tr;
        }
        return 0;
    }
public:
    Dinic(int n, int s, int t) : n(n), s(s), t(t) {
        graph.resize(n);
        level.resize(n);
        ptr.resize(n);
    }
    void addEdge(int from, int to, ll cap) {
        graph[from].pb(Edge(to, graph[to].size(), cap));
        graph[to].pb(Edge(from, graph[from].size() - 1, 0));
    }
    ll maxFlow() {
        ll total = 0;
        while (bfs()) {
            fill(ptr.begin(), ptr.end(), 0);
            while (ll pushed = dfs(s, LLONG_MAX)) total += pushed;
        }
        return total;
    }
};
const int ALPHABET_SIZE = 26; 
struct AhoCorasickNode {
    int children[ALPHABET_SIZE];
    int failure = 0; 
    int parent = -1;
    char charToParent;
    bool isWordEnd = false; 
    AhoCorasickNode(int parent = -1, char ch = '$') : parent(parent), charToParent(ch) {
        memset(children, -1, sizeof(children));
    }
};
class AhoCorasick {
private:
    vector<AhoCorasickNode> trie;
public:
    AhoCorasick() : trie(1) {} 
    void insert(const string& word) {
        int node = 0; 
        for (char ch : word) {
            int c = ch - 'a'; 
            if (trie[node].children[c] == -1) { 
                trie[node].children[c] = trie.size();
                trie.emplace_back(node, ch);
            }
            node = trie[node].children[c];
        }
        trie[node].isWordEnd = true; 
    }
    void buildFailureLinks() {
        queue<int> q;
        q.push(0); 
        while (!q.empty()) {
            int node = q.front();
            q.pop();
            for (int c = 0; c < ALPHABET_SIZE; c++) {
                int child = trie[node].children[c];
                if (child == -1) continue;
                q.push(child);

                int failure = trie[node].failure;
                while (failure != 0 && trie[failure].children[c] == -1) {
                    failure = trie[failure].failure;
                }
                trie[child].failure = node == 0 ? 0 : trie[failure].children[c];
                trie[child].isWordEnd |= trie[trie[child].failure].isWordEnd;
            }
        }
    }
    vector<int> search(const string& text) {
        vector<int> positions;
        int node = 0;
        for (int i = 0; i < text.size(); i++) {
            int c = text[i] - 'a';
            while (node != 0 && trie[node].children[c] == -1) {
                node = trie[node].failure;
            }
            if (trie[node].children[c] != -1) {
                node = trie[node].children[c];
            }
            if (trie[node].isWordEnd) {
                positions.push_back(i); 
            }
        }
        return positions;
    }
};
long long binpow_iterative(long long a, long long b, long long mod) {
    long long result = 1;
    a %= mod;
    while (b > 0) {
        if (b & 1) result = result * a % mod;
        a = a * a % mod;
        b >>= 1;
    }
    return result;
}
void mergeSortIterative(vector<int>& arr) {
    int n = arr.size();
    vector<int> aux(n);
    for (int sz = 1; sz < n; sz *= 2) {
        for (int low = 0; low < n - sz; low += sz * 2) {
            int mid = low + sz - 1;
            int high = min(low + sz * 2 - 1, n - 1);
            merge(arr.begin() + low, arr.begin() + mid + 1, arr.begin() + mid + 1, arr.begin() + high + 1, aux.begin() + low);
            for (int i = low; i <= high; i++) arr[i] = aux[i];
        }
    }
}
vector<bool> bitwiseSieve(int n) {
    vector<int> prime((n + 31) / 32, 0);
    auto isPrime = [&](int k) -> bool { return prime[k >> 5] & (1 << (k & 31)); };
    auto setComposite = [&](int k) { prime[k >> 5] |= (1 << (k & 31)); };

    setComposite(0); setComposite(1);
    for (int i = 2; i * i <= n; ++i)
        if (!isPrime(i))
            for (int j = i * i; j <= n; j += i)
                setComposite(j);

    vector<bool> primes(n + 1);
    for (int i = 2; i <= n; ++i) primes[i] = !isPrime(i);
    return primes;
}
int partition(vector<int>& arr, int left, int right) {
    int pivot = arr[right];
    int i = left - 1;
    for (int j = left; j < right; j++) { 
        if (arr[j] <= pivot) { 
            i++; 
            swap(arr[i], arr[j]);
        }
    }
    swap(arr[i + 1], arr[right]);
    return i + 1;
}
int quickSelect(vector<int>& arr, int left, int right, int k) {
    if (left == right) return arr[left];
    int pivotIndex = partition(arr, left, right);
    if (k == pivotIndex) return arr[k];
    else if (k < pivotIndex) return quickSelect(arr, left, pivotIndex - 1, k);
    else return quickSelect(arr, pivotIndex + 1, right, k);
}
struct DSU {
    vector<int> parent, rank;
    DSU(int n) : parent(n), rank(n, 0) {
        iota(parent.begin(), parent.end(), 0);
    }
    int find(int x) {
        if (parent[x] != x) {
            parent[x] = find(parent[x]);
        }
        return parent[x];
    }
    void unite(int x, int y) {
        int px = find(x), py = find(y);
        if (px == py) return;
        if (rank[px] < rank[py]) swap(px, py);
        parent[py] = px;
        if (rank[px] == rank[py]) rank[px]++;
    }
};
template<typename T>
class SparseTable {
    vector<vector<T>> table;
public:
    SparseTable(const vector<T>& v) {
        int n = v.size(), k = 32 - __builtin_clz(n);
        table.assign(k, vector<T>(n));
        for (int i = 0; i < n; i++) table[0][i] = v[i];
        for (int j = 1; j < k; j++)
            for (int i = 0; i + (1 << j) <= n; i++)
                table[j][i] = min(table[j-1][i], table[j-1][i + (1 << (j-1))]);
    }
    T query(int l, int r) { 
        int j = 31 - __builtin_clz(r - l + 1);
        return min(table[j][l], table[j][r - (1 << j) + 1]);
    }
};
const int MOD = 1e9 + 7;
inline int add(int a, int b, int mod = MOD) {
    a += b;
    if(a >= mod) a -= mod;
    return a;
}
inline int sub(int a, int b, int mod = MOD) {
    a -= b;
    if(a < 0) a += mod;
    return a;
}
inline int mul(int a, int b, int mod = MOD) {
    return (int)((long long)a * b % mod);
}
int powmod(int a, long long b, int mod = MOD) {
    int res = 1;
    while(b > 0) {
        if(b & 1) res = mul(res, a, mod);
        a = mul(a, a, mod);
        b >>= 1;
    }
    return res;
}
int inv(int a, int mod = MOD) {
    return powmod(a, mod - 2, mod);
}
const long long INF = 1e18;
struct Line {
    long long m, b; 
    Line(long long _m = 0, long long _b = -INF) : m(_m), b(_b) {}
    long long eval(long long x) const {
        return m * x + b;
    }
};
struct LiChaoTree {
    vector<Line> tree;
    int size;
    long long minX, maxX;
    LiChaoTree(long long _minX, long long _maxX) : minX(_minX), maxX(_maxX) {
        size = maxX - minX + 1;
        tree.assign(4 * size, Line());
    }
    void addLine(Line line, int v = 1, long long l = 0, long long r = -1) {
        if (r == -1) r = size - 1;
        long long m = (l + r) / 2;
        bool left = line.eval(l + minX) > tree[v].eval(l + minX);
        bool mid = line.eval(m + minX) > tree[v].eval(m + minX);
        if (mid) swap(tree[v], line);
        if (l == r) return;
        else if (left != mid) addLine(line, 2*v, l, m);
        else addLine(line, 2*v+1, m+1, r);
    }
    long long query(long long x, int v = 1, long long l = 0, long long r = -1) {
        if (r == -1) r = size - 1;
        long long m = (l + r) / 2;
        long long ret = tree[v].eval(x + minX);
        if (l == r) return ret;
        else if (x <= m) return max(ret, query(x, 2*v, l, m));
        else return max(ret, query(x, 2*v+1, m+1, r));
    }
};
struct Edge {
    int u, v, weight;
    bool operator<(const Edge &other) const {
        return weight < other.weight;
    }
};
vector<Edge> kruskal(int N, vector<Edge>& edges) {
    sort(edges.begin(), edges.end());
    DSU dsu(N);
    vector<Edge> result;
    for (Edge e : edges) {
        if (dsu.find(e.u) != dsu.find(e.v)) {
            result.push_back(e);
            dsu.unite(e.u, e.v);
        }
    }
    return result;
}
int phi(int n) {
    int result = n;
    for (int i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            while (n % i == 0) n /= i;
            result -= result / i;
        }
    }
    if (n > 1) result -= result / n;
    return result;
}
vector<int> zFunction(string s) {
    int n = s.length();
    vector<int> z(n);
    for (int i = 1, l = 0, r = 0; i < n; ++i) {
        if (i <= r)
            z[i] = min(r - i + 1, z[i - l]);
        while (i + z[i] < n && s[z[i]] == s[i + z[i]])
            ++z[i];
        if (i + z[i] - 1 > r)
            l = i, r = i + z[i] - 1;
    }
    return z;
}
struct Point {
    double x, y;
};
double cross(const Point& O, const Point& A, const Point& B){
  return (A.x - O.x) * (B.y - O.y) - (A.y - O.y) * (B.x - O.x);
}

bool pointInPolygon(const vector<Point>& poly, Point p) {
    bool result = false;
    for (int i = 0, j = poly.size() - 1; i < poly.size(); j = i++) {
        if ((poly[i].y > p.y) != (poly[j].y > p.y) &&
            (p.x < (poly[j].x - poly[i].x) * (p.y - poly[i].y) / (poly[j].y - poly[i].y) + poly[i].x))
            result = !result;
    }
    return result;
}
vector<int> topologicalSort(const vector<vector<int>>& adj) {
    vector<int> in_degree(adj.size(), 0);
    for (const auto& neighbors : adj)
        for (int v : neighbors)
            in_degree[v]++;
    
    queue<int> q;
    for (int i = 0; i < adj.size(); i++)
        if (in_degree[i] == 0) q.push(i);
    
    vector<int> order;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        order.push_back(u);
        for (int v : adj[u])
            if (--in_degree[v] == 0)
                q.push(v);
    }
    return order;
}
class SqrtDecomposition {
    vector<int> b, a; 
    int len; 

public:
    SqrtDecomposition(vector<int>& input) {
        int n = input.size();
        len = static_cast<int>(sqrt(n) + 1);
        a = input;
        b.assign(len, 0);
        for (int i = 0; i < n; i++) {
            b[i / len] += a[i];
        }
    }

    void update(int idx, int val) {
        int block = idx / len;
        b[block] += val - a[idx];
        a[idx] = val;
    }

    int query(int l, int r) {
        int sum = 0;
        int startBlock = l / len, endBlock = r / len;
        if (startBlock == endBlock) {
            for (int i = l; i <= r; i++) sum += a[i];
        } else {
            for (int i = l, end = (startBlock + 1) * len - 1; i <= end; i++) sum += a[i];
            for (int i = startBlock + 1; i <= endBlock - 1; i++) sum += b[i];
            for (int i = endBlock * len; i <= r; i++) sum += a[i];
        }
        return sum;
    }
};

int longestIncreasingSubsequence(const vector<int>& nums) {
    vector<int> dp(nums.size(), 1);
    int maxLength = 1;
    for (int i = 1; i < nums.size(); i++) {
        for (int j = 0; j < i; j++) {
            if (nums[i] > nums[j]) {
                dp[i] = max(dp[i], dp[j] + 1);
            }
        }
        maxLength = max(maxLength, dp[i]);
    }
    return maxLength;
}
int binarySearch(const vector<int>& arr, int target) {
    int left = 0, right = arr.size() - 1;
    while (left <= right) {
        int mid = left + (right - left) / 2;
        if (arr[mid] == target) return mid;
        else if (arr[mid] < target) left = mid + 1;
        else right = mid - 1;
    }
    return -1; 
}
void merge(vector<int>& arr, int l, int m, int r) {
    vector<int> left(arr.begin() + l, arr.begin() + m + 1);
    vector<int> right(arr.begin() + m + 1, arr.begin() + r + 1);
    int i = 0, j = 0, k = l;
    while (i < left.size() && j < right.size()) {
        if (left[i] <= right[j]) arr[k++] = left[i++];
        else arr[k++] = right[j++];
    }
    while (i < left.size()) arr[k++] = left[i++];
    while (j < right.size()) arr[k++] = right[j++];
}

void mergeSort(vector<int>& arr, int l, int r) {
    if (l < r) {
        int m = l + (r - l) / 2;
        mergeSort(arr, l, m);
        mergeSort(arr, m + 1, r);
        merge(arr, l, m, r);
    }
}
void quickSort(vector<int>& arr, int low, int high) {
    if (low < high) {
        int pi = partition(arr, low, high);
        quickSort(arr, low, pi - 1);
        quickSort(arr, pi + 1, high);
    }
}
vector<int> bfs(int start, const vector<vector<int>>& graph) {
    vector<int> distances(graph.size(), -1);
    queue<int> q;
    q.push(start);
    distances[start] = 0;
    while (!q.empty()) {
        int v = q.front(); q.pop();
        for (int u : graph[v]) {
            if (distances[u] == -1) {
                q.push(u);
                distances[u] = distances[v] + 1;
            }
        }
    }
    return distances;
}
void dfsUtil(int v, vector<bool>& visited, const vector<vector<int>>& graph) {
    visited[v] = true;
    for (int u : graph[v]) {
        if (!visited[u]) {
            dfsUtil(u, visited, graph);
        }
    }
}

void dfs(int start, const vector<vector<int>>& graph) {
    vector<bool> visited(graph.size(), false);
    dfsUtil(start, visited, graph);
}
struct UnionFind {
    vector<int> parent, rank;
    UnionFind(int N) : parent(N), rank(N, 0) {
        iota(parent.begin(), parent.end(), 0);
    }
    int find(int x) {
        if (parent[x] != x) parent[x] = find(parent[x]);
        return parent[x];
    }
    void unionSets(int x, int y) {
        int px = find(x), py = find(y);
        if (px == py) return;
        if (rank[px] < rank[py]) swap(px, py);
        parent[py] = px;
        if (rank[px] == rank[py]) rank[px]++;
    }
};
vector<Point> convexHull(vector<Point>& points) {
    if (points.size() <= 1) return points;
    sort(points.begin(), points.end(), [](Point a, Point b) {
        return a.x < b.x || (a.x == b.x && a.y < b.y);
    });
    vector<Point> hull;
    for (int i = 0; i < points.size(); ++i) {
        while (hull.size() >= 2 && cross(hull[hull.size()-2], hull.back(), points[i]) <= 0)
            hull.pop_back();
        hull.push_back(points[i]);
    }
    size_t lowerSize = hull.size() + 1;
    for (int i = points.size() - 1; i >= 0; --i) {
        while (hull.size() >= lowerSize && cross(hull[hull.size()-2], hull.back(), points[i]) <= 0)
            hull.pop_back();
        hull.push_back(points[i]);
    }
    hull.pop_back();
    return hull;
}
int edmondsKarp(vector<vector<int>>& capacity, int source, int sink) {
    int n = capacity.size();
    vector<vector<int>> adj(n, vector<int>());
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            if (capacity[i][j] > 0) adj[i].push_back(j), adj[j].push_back(i);
    int flow = 0;
    vector<int> parent(n);
    while (true) {
        fill(parent.begin(), parent.end(), -1);
        parent[source] = source;
        queue<pair<int, int>> q;
        q.push({source, INT_MAX});
        while (!q.empty()) {
            int cur = q.front().first, curFlow = q.front().second;
            q.pop();
            for (int next : adj[cur]) {
                if (parent[next] == -1 && capacity[cur][next]) {
                    parent[next] = cur;
                    int newFlow = min(curFlow, capacity[cur][next]);
                    if (next == sink) {
                        flow += newFlow;
                        int curNode = next;
                        while (curNode != source) {
                            int prev = parent[curNode];
                            capacity[prev][curNode] -= newFlow;
                            capacity[curNode][prev] += newFlow;
                            curNode = prev;
                        }
                        goto endBfs;
                    }
                    q.push({next, newFlow});
                }
            }
        }
        break;
        endBfs:;
    }
    return flow;
}
void findBridgesUtil(int u, vector<int>& disc, vector<int>& low, vector<int>& parent, vector<pair<int, int>>& bridges, vector<vector<int>>& adj) {
    static int time = 0;
    disc[u] = low[u] = ++time;
    for (int v : adj[u]) {
        if (!disc[v]) { 
            parent[v] = u;
            findBridgesUtil(v, disc, low, parent, bridges, adj);
            low[u] = min(low[u], low[v]);
            if (low[v] > disc[u])
                bridges.push_back({u, v});
        } else if (v != parent[u])
            low[u] = min(low[u], disc[v]);
    }
}

vector<pair<int, int>> findBridges(int V, vector<vector<int>>& adj) {
    vector<int> disc(V, 0), low(V, 0), parent(V, -1);
    vector<pair<int, int>> bridges;
    for (int i = 0; i < V; ++i)
        if (!disc[i])
            findBridgesUtil(i, disc, low, parent, bridges, adj);
    return bridges;
}
void tarjanSCCUtil(int u, vector<int>& disc, vector<int>& low, stack<int>& st, vector<bool>& inStack, vector<vector<int>>& adj, vector<vector<int>>& scc) {
    static int time = 0;
    disc[u] = low[u] = ++time;
    st.push(u);
    inStack[u] = true;

    for (int v : adj[u]) {
        if (disc[v] == -1) {
            tarjanSCCUtil(v, disc, low, st, inStack, adj, scc);
            low[u] = min(low[u], low[v]);
        } else if (inStack[v])
            low[u] = min(low[u], disc[v]);
    }

    if (low[u] == disc[u]) {
        vector<int> currentSCC;
        while (st.top() != u) {
            int v = st.top(); st.pop();
            inStack[v] = false;
            currentSCC.push_back(v);
        }
        st.pop();
        inStack[u] = false;
        currentSCC.push_back(u);
        scc.push_back(currentSCC);
    }
}
vector<vector<int>> tarjanSCC(int V, vector<vector<int>>& adj) {
    vector<int> disc(V, -1), low(V, -1);
    vector<bool> inStack(V, false);
    stack<int> st;
    vector<vector<int>> scc;

    for (int i = 0; i < V; ++i)
        if (disc[i] == -1)
            tarjanSCCUtil(i, disc, low, st, inStack, adj, scc);

    return scc;
}
bool isBipartiteUtil(int v, vector<int>& color, vector<vector<int>>& adj) {
    for (int u : adj[v]) {
        if (color[u] == -1) {
            color[u] = 1 - color[v];
            if (!isBipartiteUtil(u, color, adj))
                return false;
        } else if (color[u] == color[v])
            return false;
    }
    return true;
}

bool isBipartite(int V, vector<vector<int>>& adj) {
    vector<int> color(V, -1);
    for (int i = 0; i < V; ++i)
        if (color[i] == -1) {
            color[i] = 0;
            if (!isBipartiteUtil(i, color, adj))
                return false;
        }
    return true;
}

using namespace __gnu_pbds;

template <typename T>
using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
template<typename Key, typename Value>
using ordered_map = tree<Key, Value, less<Key>, rb_tree_tag, tree_order_statistics_node_update>;
template<typename Key, typename Value>
using gp_hash_table = gp_hash_table<Key,Value,direct_mask_range_hashing<int>, hash_standard_resize_policy<hash_exponential_size_policy<>, hash_load_check_resize_trigger<>, true>>;
typedef __gnu_pbds::priority_queue<int, less<int>, pairing_heap_tag> pbds_priority_queue;
typedef trie<string, null_type, trie_string_access_traits<>, pat_trie_tag, trie_prefix_search_node_update> pbds_trie;

int main() {

    return 0;
}
