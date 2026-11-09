/* Exact maximum clique by greedy colouring bounds (Tomita style).
   Input: N, then N rows of N characters 0/1 (the adjacency matrix).
   Output: the clique number, then the vertices of one maximum clique. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int N,W; uint64_t **adj; int best=0; int cur[4096],bs[4096];
static int pc(uint64_t x){return __builtin_popcountll(x);}
void expand(uint64_t *P,int depth){
  int cnt=0; for(int i=0;i<W;i++)cnt+=pc(P[i]); if(!cnt){ if(depth>best){best=depth;memcpy(bs,cur,4*depth);} return;}
  int *order=malloc(sizeof(int)*cnt),*col=malloc(sizeof(int)*cnt);
  uint64_t *U=malloc(8*W),*Q=malloc(8*W); memcpy(U,P,8*W); int k=0,c=0;
  while(1){int any=0;for(int i=0;i<W;i++)if(U[i]){any=1;break;} if(!any)break; c++; memcpy(Q,U,8*W);
    while(1){int v=-1;for(int i=0;i<W;i++)if(Q[i]){v=i*64+__builtin_ctzll(Q[i]);break;} if(v<0)break;
      U[v>>6]&=~(1ULL<<(v&63)); Q[v>>6]&=~(1ULL<<(v&63)); for(int i=0;i<W;i++)Q[i]&=~adj[v][i]; order[k]=v;col[k]=c;k++;}}
  uint64_t *NP=malloc(8*W);
  for(int t=k-1;t>=0;t--){ if(depth+col[t]<=best)break; int v=order[t]; cur[depth]=v;
    for(int i=0;i<W;i++)NP[i]=P[i]&adj[v][i]; expand(NP,depth+1); P[v>>6]&=~(1ULL<<(v&63)); }
  free(order);free(col);free(U);free(Q);free(NP);
}
int main(){ if(scanf("%d",&N)!=1)return 1; W=(N+63)/64; adj=malloc(sizeof(uint64_t*)*N); char *row=malloc(N+2);
  for(int a=0;a<N;a++){adj[a]=calloc(W,8); if(scanf("%s",row)!=1)return 1; for(int b=0;b<N;b++) if(row[b]=='1') adj[a][b>>6]|=1ULL<<(b&63);}
  uint64_t *P=calloc(W,8); for(int a=0;a<N;a++)P[a>>6]|=1ULL<<(a&63);
  expand(P,0); printf("%d\n",best); for(int i=0;i<best;i++)printf("%d ",bs[i]); printf("\n"); }
