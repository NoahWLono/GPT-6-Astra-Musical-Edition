#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
using Tup=tuple<int,int,int>;
const set<Tup> claimed={{4,4,3},{6,3,3},{6,5,3},{6,6,4},{6,6,6},{7,7,3},{9,4,3},{8,7,4},{8,8,5},{10,6,4},{12,4,4},{13,5,3},{13,7,4},{16,5,4},{21,6,4}};
int main(int argc,char**argv){
 int nlo=argc>1?stoi(argv[1]):6, nhi=argc>2?stoi(argv[2]):60, klimit=argc>3?stoi(argv[3]):100000;
 auto start=chrono::steady_clock::now(); long long checked=0,passsum=0,solutions=0; set<Tup> found;
 cout<<"n,k,k1,k2,k3,g1,g2,g3,claimed,boundary\n";
 for(int n=nlo;n<=nhi;n++){
  int h=n/2, km=min(h+1,klimit);
  vector<vector<vector<int>>> m(km+1,vector<vector<int>>(h+1));
  vector<vector<int>> generators(km+1);
  for(int a=3;a<=km;a++)for(int g=1;g<=h;g++)if(2*(a-1)<=n/gcd(n,g)){
   auto& v=m[a][g]; v.assign(h+1,0);for(int i=1;i<a;i++){int r=i*g%n;v[min(r,n-r)]=a-i;}
   generators[a].push_back(g);
  }
  for(int a=3;a<=km;a++)for(int b=3;b<=a;b++)for(int c=3;c<=b;c++){
   int t=a*(a-1)+b*(b-1)+c*(c-1); int k=(int)((1+sqrt(1+4.0*t))/2+1e-7);
   if(k*(k-1)!=t||k-1>h||k-1>a+b+c-3)continue;
   long long target2=1LL*(k-1)*k*(2*k-1)/6;
   for(int g1:generators[a]){
    if(n%g1)continue; // Unit group transitive on each gcd class: representative g1=gcd(n,g1).
    const auto&v1=m[a][g1];
    for(int g2:generators[b]){
     if(a==b && g2<g1)continue;
     const auto&v2=m[b][g2]; vector<int> ab(h+1);long long ab2=0;bool excess=false;
     for(int d=1;d<=h;d++){ab[d]=v1[d]+v2[d];if(ab[d]>=k){excess=true;break;}ab2+=ab[d]*ab[d];}
     if(excess)continue;
     long long c2=1LL*(c-1)*c*(2*c-1)/6;long long dotneed=(target2-ab2-c2)/2;
     if(target2<ab2+c2||(target2-ab2-c2)%2)continue;
     for(int g3:generators[c]){
      if(b==c &&g3<g2)continue;
      if(gcd(gcd(gcd(n,g1),g2),g3)!=1)continue;
      checked++;long long dot=0;
      for(int i=1;i<c;i++){int r=i*g3%n;dot+=ab[min(r,n-r)]*(c-i);}
      if(dot!=dotneed)continue;passsum++;
      const auto&v3=m[c][g3]; vector<bool> seen(k,false);bool ok=true;int positive=0;
      for(int d=1;d<=h;d++){int value=ab[d]+v3[d];if(!value)continue;if(value>=k||seen[value]){ok=false;break;}seen[value]=true;positive++;}
      if(!ok||positive!=k-1)continue;solutions++;Tup key={a,b,c};
      int boundary=(2*(a-1)==n/gcd(n,g1))||(2*(b-1)==n/gcd(n,g2))||(2*(c-1)==n/gcd(n,g3));
      cout<<n<<','<<k<<','<<a<<','<<b<<','<<c<<','<<g1<<','<<g2<<','<<g3<<','<<claimed.count(key)<<','<<boundary<<'\n';
      if(found.insert(key).second)cerr<<"FIRST "<<a<<','<<b<<','<<c<<" n="<<n<<" gens="<<g1<<','<<g2<<','<<g3<<" claimed="<<claimed.count(key)<<" boundary="<<boundary<<'\n';
     }
    }
   }
  }
  if(n%10==0){cerr<<"n="<<n<<" checked="<<checked<<" sum_pass="<<passsum<<" solutions="<<solutions<<" time="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';cout.flush();}
 }
 cerr<<"DONE checked="<<checked<<" solutions="<<solutions<<" tuples="<<found.size()<<" time="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
}
