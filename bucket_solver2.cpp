#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <unordered_map>
#include <unordered_set>
#include <deque>
#include <queue>
#include <functional>
#include <chrono>
#include <cmath>
#include <iomanip>
#include <array>
#include <cstring>

using namespace std;

static constexpr int MAX_BUCKETS = 8;

using Buckets = vector<int>;

struct Instance {
    int n = 0;
    Buckets capacities;
    Buckets goal;
    string filename;
};

struct SearchResult {
    bool found = false;
    vector<Buckets> path;
    int visitedNodes = 0;
    int maxOpenSize = 0;
    double timeMs = 0.0;
};

using State = uint64_t;

static int G_N = 0;
static int G_CAP[MAX_BUCKETS];
static int G_GOAL[MAX_BUCKETS];
static int G_BITS[MAX_BUCKETS];
static int G_SHIFT[MAX_BUCKETS];
static uint64_t G_MASK[MAX_BUCKETS];

static void initEncoding(const Instance& inst) {
    G_N = inst.n;
    int shift = 0;
    for (int i = 0; i < G_N; i++) {
        G_CAP[i] = inst.capacities[i];
        G_GOAL[i] = inst.goal[i];
        int bits = 1;
        while ((1 << bits) <= G_CAP[i]) bits++;
        G_BITS[i] = bits;
        G_SHIFT[i] = shift;
        G_MASK[i] = ((1ULL << bits) - 1) << shift;
        shift += bits;
    }
}

static inline State encode(const int* vals) {
    State s = 0;
    for (int i = 0; i < G_N; i++)
        s |= ((State)vals[i]) << G_SHIFT[i];
    return s;
}

static inline void decode(State s, int* vals) {
    for (int i = 0; i < G_N; i++)
        vals[i] = (int)((s & G_MASK[i]) >> G_SHIFT[i]);
}

static inline State encodeVec(const Buckets& b) {
    int v[MAX_BUCKETS];
    for (int i = 0; i < G_N; i++) v[i] = b[i];
    return encode(v);
}

static inline Buckets decodeVec(State s) {
    int v[MAX_BUCKETS];
    decode(s, v);
    return Buckets(v, v + G_N);
}

/// H1: somme de la difference absolu 
static inline int h_sumDiff(State s) {
    int v[MAX_BUCKETS];
    decode(s, v);
    int h = 0;
    for (int i = 0; i < G_N; i++) h += abs(v[i] - G_GOAL[i]);
    return h;
}
/// H2: nombre de buckets differents
static inline int h_wrongCount(State s) {
    int v[MAX_BUCKETS];
    decode(s, v);
    int h = 0;
    for (int i = 0; i < G_N; i++) h += (v[i] != G_GOAL[i]);
    return h;
}
/// H3: difference maximale
static inline int h_maxDiff(State s) {
    int v[MAX_BUCKETS];
    decode(s, v);
    int h = 0;
    for (int i = 0; i < G_N; i++) h = max(h, abs(v[i] - G_GOAL[i]));
    return h;
}

static int G_SUCC_BUF_COUNT;
static State G_SUCC_BUF[256];

/// Genere les etats suiivants 
static inline void genSuccessors(State cur) {
    int v[MAX_BUCKETS];
    decode(cur, v);
    int cnt = 0;

    for (int i = 0; i < G_N; i++) {
        if (v[i] < G_CAP[i]) {
            int old = v[i]; v[i] = G_CAP[i];
            G_SUCC_BUF[cnt++] = encode(v);
            v[i] = old;
        }
        if (v[i] > 0) {
            int old = v[i]; v[i] = 0;
            G_SUCC_BUF[cnt++] = encode(v);
            v[i] = old;
        }
    }
    for (int i = 0; i < G_N; i++) {
        if (!v[i]) continue;
        for (int j = 0; j < G_N; j++) {
            if (i == j || v[j] == G_CAP[j]) continue;
            int amt = min(v[i], G_CAP[j] - v[j]);
            int oi = v[i], oj = v[j];
            v[i] -= amt; v[j] += amt;
            G_SUCC_BUF[cnt++] = encode(v);
            v[i] = oi; v[j] = oj;
        }
    }
    G_SUCC_BUF_COUNT = cnt;
}

struct SHash {
    size_t operator()(State s) const {
        s ^= s >> 33;
        s *= 0xff51afd7ed558ccdULL;
        s ^= s >> 33;
        s *= 0xc4ceb9fe1a85ec53ULL;
        s ^= s >> 33;
        return (size_t)s;
    }
};

static const State SENTINEL = ~(State)0;

static vector<Buckets> reconstructPath(State goal,
    const unordered_map<State, State, SHash>& parent) {
    vector<Buckets> path;
    State cur = goal;
    while (cur != SENTINEL) {
        path.push_back(decodeVec(cur));
        auto it = parent.find(cur);
        if (it->second == cur) break;
        cur = it->second;
    }
    reverse(path.begin(), path.end());
    return path;
}

SearchResult searchDFS(State init, State goal) {
    SearchResult res;
    auto t0 = chrono::high_resolution_clock::now();

    unordered_map<State, State, SHash> parent;
    parent.reserve(1 << 16);
    parent[init] = init;

    vector<State> stack;
    stack.reserve(4096);
    stack.push_back(init);

    while (!stack.empty()) {
        int sz = (int)stack.size();
        if (sz > res.maxOpenSize) res.maxOpenSize = sz;
        State e = stack.back(); stack.pop_back();
        res.visitedNodes++;

        if (e == goal) {
            res.found = true;
            res.path = reconstructPath(e, parent);
            break;
        }

        genSuccessors(e);
        for (int i = 0; i < G_SUCC_BUF_COUNT; i++) {
            State s = G_SUCC_BUF[i];
            if (parent.find(s) == parent.end()) {
                parent[s] = e;
                stack.push_back(s);
            }
        }
    }

    res.timeMs = chrono::duration<double, milli>(
        chrono::high_resolution_clock::now() - t0).count();
    return res;
}

SearchResult searchBFS(State init, State goal) {
    SearchResult res;
    auto t0 = chrono::high_resolution_clock::now();

    unordered_map<State, State, SHash> parent;
    parent.reserve(1 << 16);
    parent[init] = init;

    deque<State> queue;
    queue.push_back(init);

    while (!queue.empty()) {
        int sz = (int)queue.size();
        if (sz > res.maxOpenSize) res.maxOpenSize = sz;
        State e = queue.front(); queue.pop_front();
        res.visitedNodes++;

        if (e == goal) {
            res.found = true;
            res.path = reconstructPath(e, parent);
            break;
        }

        genSuccessors(e);
        for (int i = 0; i < G_SUCC_BUF_COUNT; i++) {
            State s = G_SUCC_BUF[i];
            if (parent.find(s) == parent.end()) {
                parent[s] = e;
                queue.push_back(s);
            }
        }
    }

    res.timeMs = chrono::duration<double, milli>(
        chrono::high_resolution_clock::now() - t0).count();
    return res;
}

SearchResult searchBestFirst(State init, State goal,
                             function<int(State)> hFn) {
    SearchResult res;
    auto t0 = chrono::high_resolution_clock::now();

    unordered_map<State, State, SHash> parent;
    parent.reserve(1 << 16);
    parent[init] = init;

    using Entry = pair<int, State>;
    priority_queue<Entry, vector<Entry>, greater<Entry>> pq;
    pq.push({hFn(init), init});
    int pqSize = 1;

    while (pqSize > 0) {
        if (pqSize > res.maxOpenSize) res.maxOpenSize = pqSize;
        State e = pq.top().second; pq.pop(); pqSize--;
        res.visitedNodes++;

        if (e == goal) {
            res.found = true;
            res.path = reconstructPath(e, parent);
            break;
        }

        genSuccessors(e);
        for (int i = 0; i < G_SUCC_BUF_COUNT; i++) {
            State s = G_SUCC_BUF[i];
            if (parent.find(s) == parent.end()) {
                parent[s] = e;
                pq.push({hFn(s), s});
                pqSize++;
            }
        }
    }

    res.timeMs = chrono::duration<double, milli>(
        chrono::high_resolution_clock::now() - t0).count();
    return res;
}

SearchResult searchAStar(State init, State goal,
                         function<int(State)> hFn) {
    SearchResult res;
    auto t0 = chrono::high_resolution_clock::now();

    unordered_map<State, int, SHash> gCost;
    unordered_map<State, State, SHash> parent;
    gCost.reserve(1 << 16);
    parent.reserve(1 << 16);

    gCost[init] = 0;
    parent[init] = init;

    using Entry = pair<int, State>;
    priority_queue<Entry, vector<Entry>, greater<Entry>> pq;
    pq.push({hFn(init), init});
    int pqSize = 1;

    while (pqSize > 0) {
        if (pqSize > res.maxOpenSize) res.maxOpenSize = pqSize;
        auto [f, e] = pq.top(); pq.pop(); pqSize--;

        int ge = gCost[e];
        if (f > ge + hFn(e)) continue;

        res.visitedNodes++;

        if (e == goal) {
            res.found = true;
            res.path = reconstructPath(e, parent);
            break;
        }

        genSuccessors(e);
        int ng = ge + 1;
        for (int i = 0; i < G_SUCC_BUF_COUNT; i++) {
            State s = G_SUCC_BUF[i];
            auto it = gCost.find(s);
            if (it == gCost.end() || ng < it->second) {
                gCost[s] = ng;
                parent[s] = e;
                pq.push({ng + hFn(s), s});
                pqSize++;
            }
        }
    }

    res.timeMs = chrono::duration<double, milli>(
        chrono::high_resolution_clock::now() - t0).count();
    return res;
}

Instance parseBuck(const string& path) {
    Instance inst;
    inst.filename = path;
    ifstream f(path);
    if (!f) { cerr << "Cannot open: " << path << '\n'; return inst; }
    string line;
    if (getline(f, line)) inst.n = stoi(line);
    if (getline(f, line)) { istringstream ss(line); int v; while (ss >> v) inst.capacities.push_back(v); }
    if (getline(f, line)) { istringstream ss(line); int v; while (ss >> v) inst.goal.push_back(v); }
    return inst;
}

vector<Instance> loadDir(const string& dir) {
    vector<Instance> out;
    if (!filesystem::exists(dir)) { cerr << "Directory not found: " << dir << '\n'; return out; }
    for (auto& e : filesystem::directory_iterator(dir))
        if (e.path().extension() == ".buck")
            out.push_back(parseBuck(e.path().string()));
    sort(out.begin(), out.end(), [](auto& a, auto& b){ return a.filename < b.filename; });
    return out;
}

bool isValid(const Instance& i) {
    if (i.n <= 0 || (int)i.capacities.size() != i.n || (int)i.goal.size() != i.n) return false;
    if (i.n > MAX_BUCKETS) return false;
    for (int j = 0; j < i.n; j++)
        if (i.goal[j] < 0 || i.goal[j] > i.capacities[j]) return false;
    return true;
}

void printB(ostream& os, const Buckets& b) {
    os << '(';
    for (size_t i = 0; i < b.size(); i++) { if (i) os << ", "; os << b[i]; }
    os << ')';
}

string solve(const Instance& inst) {
    ostringstream out;

    initEncoding(inst);

    out << "\n========== " << inst.filename << " ==========\n";
    out << "Cap: "; printB(out, inst.capacities);
    out << "  Goal: "; printB(out, inst.goal); out << '\n';

    int initArr[MAX_BUCKETS] = {};
    State initS = encode(initArr);
    int goalArr[MAX_BUCKETS];
    for (int i = 0; i < G_N; i++) goalArr[i] = inst.goal[i];
    State goalS = encode(goalArr);

    struct Algo {
        const char* name;
        function<SearchResult()> run;
    };

    vector<Algo> algos;
    algos.push_back({"DFS", [&](){ return searchDFS(initS, goalS); }});
    algos.push_back({"BFS", [&](){ return searchBFS(initS, goalS); }});
    algos.push_back({"Best-First (H1:SumDiff)", [&](){
        return searchBestFirst(initS, goalS, h_sumDiff);
    }});
    algos.push_back({"Best-First (H2:WrongCount)", [&](){
        return searchBestFirst(initS, goalS, h_wrongCount);
    }});
    algos.push_back({"Best-First (H3:MaxDiff)", [&](){
        return searchBestFirst(initS, goalS, h_maxDiff);
    }});
    algos.push_back({"A* (H1:SumDiff)", [&](){
        return searchAStar(initS, goalS, h_sumDiff);
    }});
    algos.push_back({"A* (H2:WrongCount)", [&](){
        return searchAStar(initS, goalS, h_wrongCount);
    }});
    algos.push_back({"A* (H3:MaxDiff)", [&](){
        return searchAStar(initS, goalS, h_maxDiff);
    }});

    out << '\n' << left << setw(34) << "Algorithm"
        << right << setw(7) << "Path" << setw(10) << "Visited"
        << setw(10) << "MaxOpen" << setw(12) << "ms" << '\n'
        << string(73, '-') << '\n';

    vector<pair<string, SearchResult>> results;

    for (size_t ai = 0; ai < algos.size(); ai++) {
        SearchResult r = algos[ai].run();

        out << left << setw(34) << algos[ai].name << right;
        out << setw(7) << (r.found ? to_string(r.path.size()-1) : string("N/A"));
        out << setw(10) << r.visitedNodes
            << setw(10) << r.maxOpenSize
            << setw(12) << fixed << setprecision(1) << r.timeMs << '\n';

        results.push_back({algos[ai].name, move(r)});
    }

    for (auto& [name, r] : results) {
        if (r.found && r.path.size() <= 30) {
            out << "\n" << name << " (" << r.path.size()-1 << " steps):\n";
            for (size_t i = 0; i < r.path.size(); i++) {
                out << "  " << i << ": "; printB(out, r.path[i]); out << '\n';
            }
        }
    }

    return out.str();
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        cerr << "Usage: ./main <file1.buck> [file2.buck] ...\n";
        return 1;
    }

    string allOutput;

    for (int i = 1; i < argc; i++) {
        auto inst = parseBuck(argv[i]);
        if (isValid(inst)) {
            string result = solve(inst);
            cout << result;
            allOutput += result;
        } else {
            cerr << "Invalid instance: " << argv[i] << '\n';
        }
    }

    cout << "\nVoulez-vous enregistrer les resultats dans un fichier .txt ? (o/n) : ";
    char c;
    cin >> c;

    if (c == 'o' || c == 'O') {
        string filename = "resultats2.txt";
        bool append = false;

        if (filesystem::exists(filename)) {
            cout << "Le fichier " << filename << " existe deja. Ajouter a la suite ? (o/n) : ";
            char a;
            cin >> a;
            append = (a == 'o' || a == 'O');
        }

        ofstream file(filename, append ? ios::app : ios::trunc);
        if (file) {
            file << allOutput << '\n';
            cout << "Resultats enregistres dans " << filename << '\n';
        } else {
            cerr << "Erreur: impossible d'ecrire dans " << filename << '\n';
        }
    }

    return 0;
}