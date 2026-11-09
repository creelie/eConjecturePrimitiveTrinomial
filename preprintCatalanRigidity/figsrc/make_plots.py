import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt, numpy as np
from math import gcd
import os
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
plt.rcParams.update({'font.family':'serif','mathtext.fontset':'cm','font.size':11})
N=24
fig=plt.figure(figsize=(8,6.2)); ax=fig.add_subplot(111,projection='3d')
xs,ys,zs=[],[],[]
for a in range(1,N+1):
  for b in range(1,N+1):
    xs.append(a); ys.append(b); zs.append(gcd(a+1,b+1)-1)
zs=np.array(zs,dtype=float); cmap=plt.cm.viridis
cols=[cmap(0.15+0.85*z/zs.max()) if z>0 else (0.86,0.86,0.89,1) for z in zs]
ax.bar3d(np.array(xs)-0.4,np.array(ys)-0.4,np.zeros_like(zs),0.8,0.8,np.maximum(zs,0.05),color=cols,shade=True,linewidth=0)
ax.set_xlabel('$a$'); ax.set_ylabel('$b$'); ax.set_zlabel(r'$\dim\ker A_{a,b}$')
ax.view_init(elev=32,azim=-128)
ax.set_xticks([1,6,12,18,24]); ax.set_yticks([1,6,12,18,24])
plt.tight_layout(); plt.savefig(os.path.join(OUT, 'fig_rank.png'),dpi=200,bbox_inches='tight'); plt.close()
fig,ax=plt.subplots(figsize=(7.5,4.6))
n=np.arange(1,11)
ax.plot(n,n*(n-1)+1,'-',color='#b2182b',lw=2,label=r'upper bound $n(n-1)+1$')
nn=np.linspace(1,10,200); ax.plot(nn,nn*(nn-1)/2,'--',color='#555555',lw=1.5,label=r'$\binom{n}{2}$')
sh=[(m//2)**2 if m%2==0 else (m//2)*(m//2+2) for m in n]
ax.plot(n[1:],sh[1:],'s-',color='#2166ac',ms=5,lw=1.4,label=r'constructions $k^2$, $k(k+2)$ of Shankar')
ax.plot(range(1,7),[1,2,3,6,10,16],'o',color='#1a9850',ms=8,label=r'exact values')
ax.plot([7,8],[20,28],'^',color='#f46d43',ms=9,label='lower bounds of Appendix B')
ax.set_xlabel('$n$'); ax.set_ylabel('largest odd family in the $n\\times n$ square'); ax.set_xticks(n); ax.set_ylim(0,60)
ax.grid(alpha=0.3); ax.legend(frameon=False,fontsize=9.5,loc='upper left')
plt.tight_layout(); plt.savefig(os.path.join(OUT, 'fig_oddvalues.png'),dpi=200,bbox_inches='tight')
