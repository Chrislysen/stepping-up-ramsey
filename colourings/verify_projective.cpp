// Fresh independent Ramsey check using homogeneous determinants and a proved
// PGL(2,q) normalization. No bundled verifier or solver code was inspected.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

struct Check {
    int q;
    std::string table;
    std::vector<int> inverse;
    Check(int field, std::string colors):q(field),table(colors),inverse(field) {
        if(q<5 || q>10000) throw std::runtime_error("unsupported field size");
        for(int d=2;d*d<=q;++d) if(q%d==0) throw std::runtime_error("field order is not prime");
        if(int(table.size())!=q || table.find_first_not_of("01")!=std::string::npos)
            throw std::runtime_error("invalid table length or characters");
        inverse[1]=1;
        for(int a=2;a<q;++a) inverse[a]=q-int((std::int64_t(q/a)*inverse[q%a])%q);
        for(int a=1;a<q;++a) if(a*inverse[a]%q!=1) throw std::runtime_error("inverse failure");
        for(int x=2;x<q;++x) {
            std::array<int,6> orbit={x,inverse[x],mod(1-x),inverse[mod(1-x)],mod(x*inverse[mod(x-1)]),mod((x-1)*inverse[x])};
            for(int y:orbit) if(y<2 || y>=q || table[y]!=table[x])
                throw std::runtime_error("table is not constant on cross-ratio classes");
        }
    }
    int mod(int x) const { x%=q; return x<0?x+q:x; }
    // Homogeneous coordinates: finite a is (a,1); infinity q is (1,0).
    int det(int a,int b) const {
        int ax=(a==q?1:a),ay=(a==q?0:1);
        int bx=(b==q?1:b),by=(b==q?0:1);
        return mod(ax*by-ay*bx);
    }
    int color(int a,int b,int c,int d) const {
        int num=det(a,c)*det(b,d)%q;
        int den=det(a,d)*det(b,c)%q;
        int x=num*inverse[den]%q;
        if(x<2 || den==0) throw std::runtime_error("degenerate cross-ratio");
        return table[x]-'0';
    }
};
struct Counts {std::uint64_t visited=0,mono0=0,mono1=0;};
std::uint64_t choose(int n,int k) {
    std::uint64_t value=1;
    for(int i=1;i<=k;++i)value=value*(n-i+1)/i;
    return value;
}
Counts scan(const Check &w,int k,bool full) {
    if(k<4 || k>w.q+1 || k>8) throw std::runtime_error("unsupported forbidden size");
    int nfree=full?w.q+1:w.q-2;
    int r=full?k:k-3;
    std::vector<int> indices(r);std::iota(indices.begin(),indices.end(),0);
    Counts count;
    while(true) {
        std::array<int,8> v{};
        if(full){for(int i=0;i<r;++i)v[i]=indices[i];}
        else {v[0]=0;v[1]=1;for(int i=0;i<r;++i)v[i+2]=indices[i]+2;v[k-1]=w.q;}
        ++count.visited;
        int seen=0;
        for(int a=0;a<k-3 && seen!=3;++a)
          for(int b=a+1;b<k-2 && seen!=3;++b)
            for(int c=b+1;c<k-1 && seen!=3;++c)
              for(int d=c+1;d<k && seen!=3;++d)
                seen|=1<<w.color(v[a],v[b],v[c],v[d]);
        if(seen==1)++count.mono0;
        if(seen==2)++count.mono1;
        int i=r-1;while(i>=0 && indices[i]==nfree-r+i)--i;
        if(i<0)break;
        ++indices[i];for(int j=i+1;j<r;++j)indices[j]=indices[j-1]+1;
    }
    if(count.visited!=choose(nfree,r))throw std::runtime_error("enumeration count mismatch");
    return count;
}
int main(int argc,char**argv) {
 try {
    if(argc!=5 && argc!=6)throw std::runtime_error("usage: verify_projective q table A B [full]");
    auto start=std::chrono::steady_clock::now();
    int q=std::stoi(argv[1]),a=std::stoi(argv[3]),b=std::stoi(argv[4]);
    bool full=argc==6;if(full && std::string(argv[5])!="full")throw std::runtime_error("unknown option");
    Check w(q,argv[2]);Counts ca=scan(w,a,full),cb=(a==b?ca:scan(w,b,full));
    bool ok=ca.mono0==0 && cb.mono1==0;
    double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout<<"{\"q\":"<<q<<",\"n\":"<<q+1<<",\"sizes\":["<<a<<","<<b<<"],\"mode\":\""<<(full?"all_vertex_subsets":"PGL_normalized_0_1_infinity")<<"\",\"sets_size_A\":"<<ca.visited<<",\"sets_size_B\":"<<cb.visited<<",\"distinct_sets_visited\":"<<(a==b?ca.visited:ca.visited+cb.visited)<<",\"forbidden_color0\":"<<ca.mono0<<",\"forbidden_color1\":"<<cb.mono1<<",\"seconds\":"<<seconds<<",\"pass\":"<<(ok?"true":"false")<<"}\n";
    return ok?0:1;
 } catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 2;}
}
