#include <algorithm>
#include <bitset>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <deque>
#include <map>
#include <iostream>
#include <queue>
#include <set>
#include <stack>
#include <vector>
#include <array>
#include <unordered_map>
#include <numeric>
#include <functional>
#include <iomanip>
#include <chrono>
#include <random>
#include <sstream>
#include <climits>
#define ll long long
#define int ll
#define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define qchong(a) std::sort(all(a)),a.erase(std::unique(all(a)), a.end());
#define debug(a) for(int x:a) std::cout<<x<<" "; std::cout<<std::endl;
const int MOD=998244353;
const int INF=4e18;
struct custom_hash{
    static uint64_t splitmix64(uint64_t x) 
	{
        // 一个高质量的、混合比特的哈希函数 
        x+=0x9e3779b97f4a7c15;
        x=(x^(x>>30))*0xbf58476d1ce4e5b9;
        x=(x^(x>>27))*0x94d049bb133111eb;
        return x^(x>>31);
    }

    size_t operator()(uint64_t x) const 
	{
        // 关键：使用程序运行时间作为随机种子，让攻击者无法提前预测 
        static const uint64_t FIXED_RANDOM=std::chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x+FIXED_RANDOM);
    }
};
std::unordered_map<char,int,custom_hash> mp; //改为存坐标就把前面的 int改为 pair<int,int> 
struct Tree //树状数组 
{
	int n;
	std::vector<int> bit;
	Tree(int n):n(n+1),bit(n+1){}
	
	int query(int r)
	{
		int ret=0;
		while(r>0)
		{
			ret+=bit[r];
			r-=(r & -r);
		}
		return ret;
	}
	int query(int l,int r)
	{
		return query(r)-query(l-1);
	}
	void update(int idx,int delta)
	{
		while(idx<n)
		{
			bit[idx]+=delta;
			idx+=(idx & -idx);
		}
	}
};


const int NN=2e5+5;
ll aa[NN]; // 全局数组
struct SegTree //线段树
{
    int n;
    std::vector<ll> maxv,lazy;

    SegTree(int n):n(n),maxv(4*n+5),lazy(4*n+5,0){}

    // 建树：把 a[l..r] 的信息存进节点 p
    void build(int p,int l,int r) 
	{
        if(l==r)
		{
            maxv[p]=aa[l];
            return;
        }
        int mid=(l+r)>>1;
        build(p<<1,l,mid);
        build(p<<1|1,mid+1,r);
        maxv[p]=std::max(maxv[p<<1],maxv[p<<1|1]);
    }

    // 下传懒标记
    void pushdown(int p) 
	{
        if(lazy[p]!=0) 
		{
            ll add=lazy[p];
            // 左孩子
            maxv[p<<1]+=add;
            lazy[p<<1]+=add;
            // 右孩子
            maxv[p<<1|1]+=add;
            lazy[p<<1|1]+=add;
            // 清空当前节点的标记
            lazy[p]=0;
        }
    }

    // 区间加：给 [ql, qr] 全部加上 d
    void update(int p,int l,int r,int ql,int qr,ll d) 
	{
        if(ql<=l&&r<=qr) // 完全覆盖，直接打标记
		{ 
            maxv[p]+=d;
            lazy[p]+=d;
            return;
        }
        pushdown(p); // 不能完全覆盖，先下传标记给儿子，再往下走
        int mid=(l+r)>>1;
        if(ql<=mid) update(p<<1,l,mid,ql,qr,d);
        if(qr>mid) update(p<<1|1,mid+1,r,ql,qr,d);
        maxv[p]=std::max(maxv[p<<1],maxv[p<<1|1]);
    }

    // 区间查询最大值
    ll query(int p,int l,int r,int ql,int qr) 
	{
        if(ql<=l&&r<=qr) 
		{
            return maxv[p];
        }
        pushdown(p);
        int mid=(l+r)>>1;
        ll res=LLONG_MIN;
        if(ql<=mid) res=std::max(res,query(p<<1,l,mid,ql,qr));
        if(qr>mid) res=std::max(res,query(p<<1|1,mid+1,r,ql,qr));
        return res;
    }
};
struct DSU //并查集 
{
	std::vector<int> fa,sz;
	
	DSU(int n)
	{
		fa.resize(n+1);
		sz.resize(n+1,1);
		for(int i=1;i<=n;i++) fa[i]=i;
	} 
	int find(int x)
	{
		if(fa[x]==x) return x;
		return fa[x]=find(fa[x]);
	}
	//返回新集合大小 (若要返回索引就改为 return rx)
	int unite(int x,int y)
	{
		int rx=find(x),ry=find(y);
		if(rx==ry) return sz[rx];
		if(sz[rx]<sz[ry]) std::swap(rx,ry);
		fa[ry]=rx;
		sz[rx]+=sz[ry];
		return sz[rx]; //int newsize=unite(u,v); 
	}
	bool same(int x,int y)
	{
		return find(x)==find(y);
	}
};
int gcd(int a,int b)
{return b==0?a:gcd(b,a%b);}
int exgcd(int a,int b,int &x,int& y) //拓展欧几里得定理 
{
	if(b==0)
	{
		x=1;
		y=0;
		return a;
	}
	int x1,y1;
	int d=exgcd(b,a%b,x1,y1);
	x=y1;
	y=x1-(a/b)*y1;
	return d;
}
ll qpow(ll a,ll b)
{
	if(b==0) return 1;
	if(b==1) return a;
	if(b&1) return qpow(a,b-1)*a%MOD;
	ll half=qpow(a,b/2);
	return half*half%MOD;
}
//组合数，排列数预处理 
int fact[1000005];
int inv_fact[1000005];
void init(int n)
{
	fact[0]=1;
	for(int i=1;i<=n;i++)
	{
		fact[i]=fact[i-1]*i%MOD;
	}
	inv_fact[n]=qpow(fact[n],MOD-2);
	for(int i=n;i>=1;i--)
	{
		inv_fact[i-1]=inv_fact[i]*i%MOD;
	}
}
int C(int n,int k)
{
	if(k<0||k>n) return 0;
	return fact[n]*inv_fact[k]%MOD*inv_fact[n-k]%MOD; 
}
int P(int n,int k)
{
	if(k<0||k>n) return 0;
	return ((fact[n]%MOD)*(inv_fact[n-k]%MOD))%MOD;
}
//------------ 
std::vector<std::pair<int,int>> factorize(int n) //唯一分解定理 return vector->{p,cnt}
{
	std::vector<std::pair<int,int>> res;
	for(int p=2;p*p<=n;p++)
	{
		if(n%p==0)
		{
			int cnt=0;
			while(n%p==0)
			{
				n/=p;
				cnt++;
			}
			res.push_back({p,cnt});
		}
	}
	if(n>1) res.push_back({n,1});
	return res;
} 
std::vector<int> get_divisors(int n)  //试除法求约数（O(n^(1/2)) 暴力枚举） 
{
	std::vector<int> res;
	for(int i=1;i*i<=n;i++)
	{
		if(n%i==0)
		{
			res.push_back(i);
			if(i!=n/i) res.push_back(n/i);
		}
	}
	std::sort(all(res));
	return res;
}
//for(auto& x:factorize(n))
//	{
//		std::cout<<x.first<<" "<<x.second<<std::endl;
//	}



//素数筛
/*std::vector<bool> is_prime(n+1,true);
void prime(int n)
{
	is_prime[0]=is_prime[1]=false;
	for(int i=2;i*i<=n;i++)
	{
		if(is_prime[i])
		{
			for(int j=i*i;j<=n;j+=i) is_prime[j]=false;
		}
	}
}
*/
//线性筛预处理 
//const int N=2*1e5+7;
//std::vector<int> divs[N];
/*
void pre()
{
	for(int i=2;i<N;i++)
	{
		for(int j=i;j<N;j+=i) divs[j].push_back(i);
	}
}
//预处理找每个数的全部质因数
const int MAXN=200005;
int spf[MAXN];

void sspf()
{
	for(int i=2;i<MAXN;i++)
	{
		if(!spf[i])
		{
			spf[i]=i;
			for(int j=i;j<MAXN;j+=i)
			{
				if(!spf[j]) spf[j]=i;
			}
		}
	}
}
std::vector<int> factorize(int x)
{
	std::vector<int> res;
	while(x>1)
	{
		int p=spf[x];
		res.push_back(p);
		while(x%p==0) x/=p;
	}
	return res;
}
std::vector<std::vector<int>> factors(MAXN);
void factor()
{
	sspf();
	for(int x=2;x<MAXN;x++) factors[x]=factorize(x);
}
*/

//欧拉函数phi
int euler_phi(int n)
{
	int m=(int)std::sqrt(n+5);
	int ans=n;
	for(int i=2;i<=m;i++)
	{
		if(n%i==0)
		{
			ans=ans/i*(i-1);
			while(n%i==0) n/=i;
		}
	}
	if(n>1) ans=ans/n*(n-1);
	return ans;
} 
//1~n中所有数的phi函数值
void phi_table(int n,int* phi)
{
	for(int i=2;i<=n;i++) phi[i]=0;
	phi[1]=1;
	for(int i=2;i<=n;i++)
	{
		if(!phi[i])
		{
			for(int j=i;j<=n;j+=i)
			{
				if(!phi[j]) phi[j]=j;
				phi[j]=phi[j]/i*(i-1);
			}
		}
	}
} 
void ff()//暂存函数
{
int n=1005,x=1;
std::vector<int> Set;
//计数数组,维护最大最小值（数组元素只增加或只减少）
std::vector<int> cnt1(n+2,0),cnt2(n+2,0);
//单增数组初始化（加入全部元素）
for(auto&p :Set) cnt1[p]++;
int min1=1,max1=n,min2=n+1,max2=0;
while(min1<=n&&cnt1[min1]==0) min1++;
while(max1>=1&&cnt1[max1]==0) max1--;
//删除-对单减数组
cnt1[x]--;
while(min1<=n&&cnt1[min1]==0) min1++;
while(max1>=1&&cnt1[max1]==0) max1--;
//增加-对单增数组
if(cnt2[x]==0)
{
	min2=std::min(min2,x);
	max2=std::max(max2,x);
}
cnt2[x]++;

//离散化
//1.原始数据
std::vector<int> a(n); 
//2.拷贝并排序去重（即qchong(a)）
//std::vector<int> vals=a;
//std::sort(vals.begin(),vals.end());
//vals.erase(std::unique(all(vals),vals.end());
qchong(a);
// 3. 查询某个原始值 x 对应的离散化下标（0-based 或 1-based）
int id=std::lower_bound(all(a), x)-a.begin(); // 0-based 
int id1=std::lower_bound(all(a), x)-a.begin()+1; //1-based 

//BIT统计逆序对
qchong(a);
Tree bit(n);
int ans=0;
for(int i=0;i<n;i++)
{
	int id=std::lower_bound(all(a),a[i])-a.begin()+1; //必须1-based 
	int mid=bit.query(id);
	ans+=i-mid;
	bit.update(id,1);
}

}

//----------------------------------------------------
void often()
{
	// 1.降序定义（大到小）
	std::multiset<int,std::greater<int>> s; 
	s.insert(1); s.insert(2);
	// 2.取 multiset 中最大的元素（也就是最后一个-前提是升序）
	auto it=std::prev(s.end());
	// 3.第二个元素
	auto it=std::next(s.begin());  
	// 4.多插入
	s.insert({1,2,3});
	// 5.删掉最大的元素（配合 prev）
	s.erase(std::prev(s.end()));
	// 6.返回 x 的个数，但是慢(复杂度O(log n+cnt(x))
	int cnt = s.count(x);
	//7.遍历，但是要用迭代器
	for(auto it=s.begin();it!=s.end();it++) std::cout<<*it<<" ";
	//8.维护最小k个元素
	std::multiset<int> now;//
	int k;//
	for(int x:s) 
	{
    	now.insert(x);
    	if((int)now.size()>k) now.erase(std::prev(now.end()));// 删掉最大
	}

	//多项合并（a相同，累加b）的代码
	//std::vector<pair<int,int>> a;
	int i=0;
	while(i<a.size())
	{
		int j=i;
		int val=a[i].first;
		int cnt=0;
		int total_need=0;

		while(j<a.size()&&a[j].first==val) 
		{
    		cnt++;
    		total_need += a[j].second;
    		j++;
		}
		//写贪心逻辑
		i=j; //双指针跳转
	}
	

}
void solve() 
{
	std::cout<<"^o^"<<std::endl;
}
signed main()
{
	std::ios::sync_with_stdio(false);
	std::cin.tie(NULL);
	//#pragma comment(linker, "/STACK:268435456")
	//init(1000005);
	int T;
	std::cin>>T;
	while(T--) solve();
	return 0;
}
/*
1.前缀和  
-在讨论子句段的 XOR 时，通常可以考虑前缀 XOR;
-[l,r]的前缀和为pre[r]-pre[l-1]; 

2.双指针匹配时要在匹配成功后移动指针 
3. 

*/
