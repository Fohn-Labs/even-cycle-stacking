#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>
using C=std::vector<int>;
int F(int x){return x<=1?2*x-3:(x%2? (x-3)/2:x/2);}
struct Msg{bool occupied=false;int value=0;};
Msg message(const C& c,const C& vertices){
    Msg m;
    for(auto i=vertices.rbegin();i!=vertices.rend();++i){
        int x=c[*i];if(!m.occupied&&x==0)continue;
        m={true,F(x+(m.occupied?m.value:0))};
    }
    return m;
}
struct Trial {
    C c,original;int n,N,A,S;uint64_t moves=0;bool pivoted=false;std::string kind;
    Trial(C v):c(v),original(v),n(int(v.size())/2),N(int(v.size())),A(1<<n),S(2*A-1){
        require(std::accumulate(c.begin(),c.end(),0)==S,"initial mass");
    }
    void require(bool ok,const std::string& what)const{
        if(ok)return;
        std::string s="FAIL "+what+" n="+std::to_string(n)+" initial=";
        for(int x:original)s+=std::to_string(x)+",";
        s+=" current=";for(int x:c)s+=std::to_string(x)+",";
        throw std::runtime_error(s);
    }
    void move(int u,int v,int count=1,C* active=nullptr){
        require(count>=0&&u>=0&&u<N&&v>=0&&v<N&&((u-v+N)%N==1||(u-v+N)%N==N-1),"adjacency/count");
        while(count--){
            require(c[u]>=2,"global legal source");
            if(active){require((*active)[u]>=2,"active legal source");(*active)[u]-=2;++(*active)[v];}
            c[u]-=2;++c[v];++moves;
        }
    }
    struct Chain{
        Trial& t;C vertex,input,gain;std::vector<bool> occupied;
        Chain(Trial& tt,const C& state,C vv):t(tt),vertex(std::move(vv)),input(vertex.size()),gain(vertex.size()),occupied(vertex.size()){
            for(int i=int(vertex.size())-1;i>=0;--i){
                bool child=i+1<int(vertex.size())&&occupied[i+1];
                occupied[i]=state[vertex[i]]>0||child;
                input[i]=state[vertex[i]]+(child?gain[i+1]:0);
                gain[i]=occupied[i]?F(input[i]):0;
            }
        }
        int first()const{return vertex.empty()?0:gain[0];}
        void realize(C& state,int i,int parent,bool active){
            if(i==int(vertex.size())||!occupied[i])return;
            int v=vertex[i],x=input[i],g=gain[i],before=state[parent];
            t.require(before+g>0,"branch funding");
            C* ap=active?&state:nullptr;
            if(x>=2){
                realize(state,i+1,v,active);t.require(state[v]==x,"effective input");
                t.move(v,parent,x/2,ap);
                if(x%2){t.move(parent,v,1,ap);t.move(v,parent,1,ap);}
            }else{
                t.move(parent,v,2-x,ap);realize(state,i+1,v,active);
                t.require(state[v]==2,"injection");t.move(v,parent,1,ap);
            }
            t.require(state[v]==0&&state[parent]==before+g,"branch result");
        }
    };
    void unit(int target,const C& vertices,int fuel,int source=-1){
        C active(N,0);for(int v:vertices)active[v]=c[v];
        if(source<0){require(c[target]>=fuel,"pull reserve");active[target]=fuel;}
        else{require(c[source]>=fuel,"push reserve");active[target]=0;active[source]=fuel;}
        Chain chain(*this,active,vertices);
        require(active[target]+chain.first()>0,"unit positive score");
        chain.realize(active,0,target,true);
        require(active[target]>=1&&active[target]%3==1,"unit residue");
        while(active[target]>1){move(target,vertices[0],2,&active);move(vertices[0],target,1,&active);}
        require(active[target]==1&&std::accumulate(active.begin(),active.end(),0)==1,"unit final");
    }
    void pull(int root,const C& arm){
        Msg m=message(c,arm);if(!m.occupied)return;
        int p=m.value<=1?1-m.value:((1-m.value)%3+3)%3;
        int mass=0;for(int v:arm)mass+=c[v];
        uint64_t before=moves;unit(root,arm,p);
        require(moves-before==uint64_t(p+mass-1),"pull count");
        for(int v:arm)require(c[v]==0,"pull support");
    }
    int push(const C& path){
        int source=path.front(),target=path.back(),T=1<<(int(path.size())-1),mass=0;
        for(size_t i=1;i+1<path.size();++i)mass+=c[path[i]];
        int bound=mass<=T-2?T-mass:2,chosen=-1;
        for(int s=0;s<=std::min(bound,c[source]);++s){
            Msg m;
            for(size_t i=0;i+1<path.size();++i){
                int x=i?c[path[i]]:s;
                if(!m.occupied&&x==0)continue;
                m={true,F(x+(m.occupied?m.value:0))};
            }
            if(m.occupied&&m.value>0&&m.value%3==1){chosen=s;break;}
        }
        require(chosen>=0,"push feasible budget");
        C vertices(path.begin(),path.end()-1);std::reverse(vertices.begin(),vertices.end());
        uint64_t before=moves;int old=c[target];unit(target,vertices,chosen,source);
        require(c[target]==old+1&&moves-before==uint64_t(chosen+mass-1),"push count/target");
        for(size_t i=1;i+1<path.size();++i)require(c[path[i]]==0,"push support");
        return chosen;
    }
    C arm(int direction)const{
        C out;for(int i=1;i<n;++i)out.push_back((direction*i+N)%N);return out;
    }
    int mass(const C& vs)const{int m=0;for(int v:vs)m+=c[v];return m;}
    C with_source(const C& vs,bool antipode=false)const{
        C out{0};out.insert(out.end(),vs.begin(),vs.end());if(antipode)out.push_back(n);return out;
    }
    void clear(int v,int recipient){
        int b=c[v];move(v,recipient,b/2);
        if(b%2){move(recipient,v);move(v,recipient);}
        require(c[v]==0,"local clearing");
    }
    bool balanced(int root)const{
        int left=c[(root+n)%N],right=left;
        for(int i=1;i<n;++i){left+=c[(root-i+N)%N];right+=c[(root+i)%N];}
        return left<=A-1&&right<=A-1;
    }
    void rotate(int root){C out(N);for(int i=0;i<N;++i)out[i]=c[(root+i)%N];c=std::move(out);}
    void choose_root(){
        for(int root=0;root<N;++root)if(balanced(root)){
            rotate(root);require(c[0]>c[n],"balanced occupied root");return;
        }
        require(false,"balanced existence");
    }
    void stack_path(const C& path,int preferred=-1){
        int chosen=-1,position=-1;
        for(size_t i=0;i<path.size();++i){
            if(preferred>=0&&path[i]!=preferred)continue;
            C left(path.begin(),path.begin()+i);std::reverse(left.begin(),left.end());
            C right(path.begin()+i+1,path.end());
            if(c[path[i]]+message(c,left).value+message(c,right).value>0){chosen=path[i];position=int(i);break;}
        }
        require(chosen>=0,"remaining path certificate");
        C left(path.begin(),path.begin()+position);std::reverse(left.begin(),left.end());
        C right(path.begin()+position+1,path.end());
        Chain l(*this,c,left),r(*this,c,right);
        auto cat=[](int x){return x>0?0:x==0?1:2;};
        if(cat(l.first())<=cat(r.first())){l.realize(c,0,chosen,false);r.realize(c,0,chosen,false);}
        else{r.realize(c,0,chosen,false);l.realize(c,0,chosen,false);}
    }
    void reduce(int depth=0){
        require(depth<=1&&balanced(0),"balanced recursion");
        int b=c[n],K=b+c[n-1]+c[n+1];
        if(n>=4&&K>=A){
            require(!pivoted,"one geometric pivot");
            rotate(n-1);pivoted=true;require(balanced(0),"pivot balance");
            require(c[n]+c[n-1]+c[n+1]<=A-1,"pivot small triple");
            b=c[n];K=b+c[n-1]+c[n+1];
        }
        auto left=arm(1),right=arm(-1);
        auto get=[&](int d)->C{return d==1?left:right;};
        int direction=1;
        if(b==0&&c[0]==1){
            C path;for(int i=n+1;i<N;++i)path.push_back(i);path.push_back(0);
            for(int i=1;i<n;++i)path.push_back(i);
            stack_path(path,0);kind="b0_a1_direct";return;
        }
        if(b==0){pull(0,left);kind="b0_pull";}
        else if(b==1){push(with_source(left,true));move(n,n+1);kind="b1_push";}
        else if(b==2){move(n,n+1);pull(0,left);kind="b2_pull";}
        else if(b==3&&c[n-1]==0&&c[n+1]==0){
            move(n,n-1);push(with_source(left));move(n-1,n);move(n,n+1);kind="b3_donate";
        }else{
            int chosen=0;
            for(int d:{1,-1}){
                C a=get(d);int retained=(n+d)%N;
                if(c[a.back()]%2==0&&(b!=3||c[retained]>0)){chosen=d;break;}
            }
            if(chosen){
                direction=chosen;C a=get(direction);move(a.back(),a[a.size()-2],c[a.back()]/2);
                a.pop_back();pull(0,a);clear(n,(n+direction)%N);kind="even_end";
            }else{
                require(c[n-1]%2&&c[n+1]%2,"odd endings exhaustive");
                int chosen_large=0;
                for(int d:{1,-1}){C a=get(d);int prefix=mass(a)-c[a.back()];if(prefix>=A/2-2){chosen_large=d;break;}}
                if(chosen_large){direction=chosen_large;kind="odd_large_prefix";}
                else if(K<=A-1){
                    direction=c[n-1]<=c[n+1]?1:-1;kind="odd_small_triple";
                }else{
                    require(n==3,"only C6 odd fallback");
                    require(!pivoted,"one C6 pivot");
                    rotate(n-1);pivoted=true;require(c[n]<=1&&balanced(0),"C6 pivot interface");
                    reduce(depth+1);return;
                }
                C a=get(direction);push(with_source(a));move(a.back(),n,c[a.back()]/2);
                clear(n,(n+direction)%N);
            }
        }
        require(moves<=uint64_t(A),"prefix move budget");
        C kept{0};C other=get(-direction);kept.insert(kept.end(),other.begin(),other.end());
        std::vector<bool> inside(N,false);for(int v:kept)inside[v]=true;
        for(int v=0;v<N;++v)require(inside[v]||c[v]==0,"prefix retained support");
        require(mass(kept)>=A-1,"prefix remaining mass");
        stack_path(kept);
    }
    void run(){
        choose_root();reduce();
        int support=0,total=0;for(int x:c){require(x>=0,"negative pile");support+=x>0;total+=x;}
        require(support==1&&uint64_t(total)+moves==uint64_t(S),"final stack and ledger");
    }
};
struct Result{uint64_t configs=0,moves=0,pivots=0;std::map<std::string,uint64_t> branches;};
void verify(const C& c,Result& r){Trial t(c);t.run();++r.configs;r.moves+=t.moves;r.pivots+=t.pivoted;++r.branches[t.kind];}
void generate(C& c,int index,int remain,Result& r){
    if(index+1==int(c.size())){c[index]=remain;verify(c,r);return;}
    for(int x=0;x<=remain;++x){c[index]=x;generate(c,index+1,remain-x,r);}
}
int main(int argc,char** argv){
    if(argc<2)throw std::runtime_error("usage: verify_cycle N_HALF [WORKERS] [SAMPLES]");
    int n=std::stoi(argv[1]),N=2*n,A=1<<n,S=2*A-1;
    if(n<2||n>10)throw std::runtime_error("n range 2..10");
    int workers=argc>2?std::stoi(argv[2]):1,samples=argc>3?std::stoi(argv[3]):0;
    workers=std::max(1,std::min(8,workers));
    std::vector<Result> results(workers);std::vector<std::thread> threads;std::atomic<size_t> next{0};
    std::vector<std::pair<int,int>> prefixes;
    if(!samples)for(int a=0;a<=S;++a)for(int b=0;b<=S-a;++b)prefixes.emplace_back(a,b);
    for(int w=0;w<workers;++w)threads.emplace_back([&,w]{
        if(samples){
            std::mt19937 rng(871331+w);for(int trial=w;trial<samples;trial+=workers){
                C c(N,0);int active=2+rng()%(N-1);C positions(N);std::iota(positions.begin(),positions.end(),0);std::shuffle(positions.begin(),positions.end(),rng);
                if(trial%3==0)for(int i=0;i<S;++i)++c[rng()%N];
                else for(int i=0;i<S;++i)++c[positions[rng()%active]];
                verify(c,results[w]);
            }
        }else{
            C c(N);for(;;){
                size_t j=next.fetch_add(1);if(j>=prefixes.size())break;
                c[0]=prefixes[j].first;c[1]=prefixes[j].second;
                generate(c,2,S-c[0]-c[1],results[w]);
            }
        }
    });
    for(auto& t:threads)t.join();
    Result total;for(auto& r:results){total.configs+=r.configs;total.moves+=r.moves;total.pivots+=r.pivots;for(auto& x:r.branches)total.branches[x.first]+=x.second;}
    uint64_t expected=samples;
    if(!samples){expected=1;for(int i=1;i<N;++i)expected=expected*(S+i)/i;}
    if(total.configs!=expected)throw std::runtime_error("enumeration count");
    std::cout<<"n "<<n<<"\nmode "<<(samples?"sampled":"exhaustive")<<"\nconfigurations "<<total.configs<<"\nexpected "<<expected
        <<"\nindividual_legal_moves "<<total.moves<<"\npivoted "<<total.pivots<<"\n";
    for(auto& b:total.branches)std::cout<<"branch_"<<b.first<<" "<<b.second<<"\n";
    std::cout<<"PASS: every generated configuration reached one occupied vertex using checked legal moves.\n";
}
