#include <bits/stdc++.h>
using namespace std;

int graph[60][60];
int num[6] = {20, 20, 20, 20, 10, 10};

random_device rd;

void genGraph(int, int, int);
void genTree(int);
int getLeader(int, int*);

int main()
{

    int s=0;
    for(int i=0; i<6; ++i) {
        for(int j=0; j<num[i]; ++j) {
            memset(graph, 0, sizeof graph);
            genGraph(i, j, s);
            
            int m = s+j;
            int n = (i+1)*10;

            string filename = "datafile";
            string mini = "minizinc/input/";
            string asp = "asp/input/";
            ofstream mout(mini.append(filename).append(to_string(m).append(".dzn")));
            ofstream aout(asp.append(filename).append(to_string(m).append(".lp")));

            mout << "N = " << n << ";\n";
            mout << "graph = [|\n";
            aout << "#const n=" << n << ".\n";
            for(int x=0; x<n-1; ++x) {
                mout << "  ";
                for(int y=0; y<n; ++y) {
                    mout << graph[x][y] << ", ";
                    if(x<y and graph[x][y]) {
                        aout << "edge(" << (x+1) << ", " << (y+1) << ").\n";
                    }
                }
                mout << "|\n";
                aout << "\n";
            }
            mout << "  ";
            for(int y=0; y<n-1; ++y) {
                mout << graph[n-1][y] << ", ";
            }
            mout << graph[n-1][n-1] << "  |];\n";
            mout.close();
            aout.close();
        }

        s += num[i];
    }

    return 0;
}

void genGraph(int i, int j, int s)
{
    cerr << "Inizio gen\n";
    int n = (i+1)*10;
    int ub = n*(n-1)/2;
    int target = ub*(j+1)/num[i];

    vector<pair<int, int>> coos;
    for(int x=0; x<n; ++x) {
        for(int y=x+1; y<n; ++y) {
            coos.push_back({x, y});
        }
    }
    random_shuffle(coos.begin(), coos.end());

    genTree(n);
    cerr << "fine tree " << n << "\n";
    for(int x=n-1, y=0; x<target; ) {
        int a = coos[y].first;
        int b = coos[y].second;
        if(graph[a][b] != 1) {
            graph[a][b] = graph[b][a] = 1;
            ++x;
        }
        ++y;
        cerr << "quiii " << j << " : " << target << "\n";
    }

    cerr << "Qui?\n";
}

void genTree(int n)
{
    int leader[n];
    for(int i=0; i<n; ++i)
        leader[i] = i;
        
    vector<pair<int, int>> coos;
    for(int x=0; x<n; ++x) {
        for(int y=x+1; y<n; ++y) {
            coos.push_back({x, y});
        }
    }
    random_shuffle(coos.begin(), coos.end());
    
    int comps = n, k=0;
    while(comps > 1) {
        int x = coos[k].first;
        int y = coos[k].second;
        ++k;
        int xx = getLeader(x, leader);
        int yy = getLeader(y, leader);

        if(xx != yy) {
            comps--;
            leader[x] = y;
            graph[x][y] = graph[y][x] = 1;
        }
    }
}

int getLeader(int x, int* leader)
{
    while(x != leader[x])
        x = leader[x];

    return x;
} 