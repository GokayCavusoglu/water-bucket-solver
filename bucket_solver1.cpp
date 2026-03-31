#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <queue>
#include <functional>
#include <chrono>
#include <cmath>
#include <iomanip>

using namespace std;

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

/// H1: somme de la difference absolu 
inline int h_sumDiff(const Buckets& b, const Buckets& g) {
    int h = 0;
    for (size_t i = 0; i < b.size(); i++) h += abs(b[i] - g[i]);
    return h;
}
/// H2: nombre de buckets differents
inline int h_wrongCount(const Buckets& b, const Buckets& g) {
    int h = 0;
    for (size_t i = 0; i < b.size(); i++) h += (b[i] != g[i]);
    return h;
}
/// H3: difference maximale
inline int h_maxDiff(const Buckets& b, const Buckets& g) {
    int h = 0;
    for (size_t i = 0; i < b.size(); i++) h = max(h, abs(b[i] - g[i]));
    return h;
}
/// Genere les etats suiivants 
inline void genSuccessors(const Buckets& cur, const Buckets& cap,
                          vector<Buckets>& out) {
    out.clear();
    const int n = (int)cur.size();

    for (int i = 0; i < n; i++) {
        if (cur[i] < cap[i]) { out.push_back(cur); out.back()[i] = cap[i]; }
        if (cur[i] > 0)      { out.push_back(cur); out.back()[i] = 0; }
    }
    for (int i = 0; i < n; i++) {
        if (!cur[i]) continue;
        for (int j = 0; j < n; j++) {
            if (i == j || cur[j] == cap[j]) continue;
            int amt = min(cur[i], cap[j] - cur[j]);
            out.push_back(cur);
            out.back()[i] -= amt;
            out.back()[j] += amt;
        }
    }
}

struct BHash {
    size_t operator()(const Buckets& b) const {
        size_t h = 0;
        for (int x : b) h = h * 31 + (size_t)(x + 1);
        return h;
    }
};

class Open {
public:
    virtual ~Open() = default;
    virtual void push(const Buckets& s) = 0;
    virtual Buckets pop() = 0;
    virtual bool empty() const = 0;
    virtual int size() const = 0;
};

class Open_Pile : public Open {
    vector<Buckets> v;
public:
    void push(const Buckets& s) override { v.push_back(s); }
    Buckets pop() override { auto s = move(v.back()); v.pop_back(); return s; }
    bool empty() const override { return v.empty(); }
    int size() const override { return (int)v.size(); }
};

class Open_File : public Open {
    deque<Buckets> q;
public:
    void push(const Buckets& s) override { q.push_back(s); }
    Buckets pop() override { auto s = move(q.front()); q.pop_front(); return s; }
    bool empty() const override { return q.empty(); }
    int size() const override { return (int)q.size(); }
};

class Open_Liste : public Open {
    using Entry = pair<int, Buckets>;
    priority_queue<Entry, vector<Entry>, greater<Entry>> pq;
    int cnt = 0;
    function<int(const Buckets&)> hFn;
public:
    Open_Liste(function<int(const Buckets&)> f) : hFn(move(f)) {}
    void push(const Buckets& s) override { pq.push(Entry(hFn(s), s)); cnt++; }
    Buckets pop() override { Buckets s = pq.top().second; pq.pop(); cnt--; return s; }
    bool empty() const override { return pq.empty(); }
    int size() const override { return cnt; }
};

SearchResult search(const Buckets& init, const Buckets& cap,
                    const Buckets& goal, Open& ouvert) {
    SearchResult res;
    auto t0 = chrono::high_resolution_clock::now();

    unordered_map<Buckets, Buckets, BHash> parent;
    parent[init] = init;

    ouvert.push(init);
    vector<Buckets> succs;

    while (!ouvert.empty()) {
        res.maxOpenSize = max(res.maxOpenSize, ouvert.size());
        Buckets e = ouvert.pop();
        res.visitedNodes++;

        if (e == goal) {
            res.found = true;
            Buckets cur = e;
            while (parent[cur] != cur) {
                res.path.push_back(cur);
                cur = parent[cur];
            }
            res.path.push_back(cur);
            reverse(res.path.begin(), res.path.end());
            break;
        }

        genSuccessors(e, cap, succs);
        for (auto& s : succs) {
            if (parent.find(s) == parent.end()) {
                parent[s] = e;
                ouvert.push(s);
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

    out << "\n========== " << inst.filename << " ==========\n";
    out << "Cap: "; printB(out, inst.capacities);
    out << "  Goal: "; printB(out, inst.goal); out << '\n';

    Buckets init(inst.n, 0);
    const Buckets& g = inst.goal;

    struct Algo {
        const char* name;
        function<Open*()> make;
    };

    vector<Algo> algos;
    algos.push_back({"DFS", [](){ return (Open*)new Open_Pile(); }});
    algos.push_back({"BFS", [](){ return (Open*)new Open_File(); }});
    algos.push_back({"Best-First (H1:SumDiff)", [&](){
        return (Open*)new Open_Liste([&](const Buckets& b){ return h_sumDiff(b,g); });
    }});
    algos.push_back({"Best-First (H2:WrongCount)", [&](){
        return (Open*)new Open_Liste([&](const Buckets& b){ return h_wrongCount(b,g); });
    }});
    algos.push_back({"Best-First (H3:MaxDiff)", [&](){
        return (Open*)new Open_Liste([&](const Buckets& b){ return h_maxDiff(b,g); });
    }});

    out << '\n' << left << setw(34) << "Algorithm"
        << right << setw(7) << "Path" << setw(10) << "Visited"
        << setw(10) << "MaxOpen" << setw(10) << "ms" << '\n'
        << string(71, '-') << '\n';

    vector<pair<string, SearchResult>> results;

    for (size_t ai = 0; ai < algos.size(); ai++) {
        Open* o = algos[ai].make();
        SearchResult r = search(init, inst.capacities, g, *o);
        delete o;

        out << left << setw(34) << algos[ai].name << right;
        out << setw(7) << (r.found ? to_string(r.path.size()-1) : string("N/A"));
        out << setw(10) << r.visitedNodes
            << setw(10) << r.maxOpenSize
            << setw(10) << fixed << setprecision(1) << r.timeMs << '\n';

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
        string filename = "resultats.txt";
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