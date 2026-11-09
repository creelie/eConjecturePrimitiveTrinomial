import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'verification', 'catalan-rigidity'))
from two_rows_constructions import oneclass, polyB, polyC
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
plt.rcParams.update({'font.family':'serif','mathtext.fontset':'cm','font.size':11})
fams=[(10,oneclass(10),'(a) $a=10$, even family, $8$ paths','#1f4e9c'),
      (9,polyB(9),'(b) $a=9$, even family, $11$ paths','#2a7f3f'),
      (10,polyC(10),'(c) $a=10$, odd family, $12$ paths','#b0172f')]
fig,axs=plt.subplots(1,3,figsize=(13,7.2))
for ax,(a,F,title,col) in zip(axs,fams):
    F=sorted(F); gap=3.0
    for r,(i,ii) in enumerate(F):
        y0=-r*gap
        for x in range(a+1): ax.plot([x,x],[y0,y0+2],color='#d0d0d0',lw=0.6,zorder=1)
        for y in range(3): ax.plot([0,a],[y0+y,y0+y],color='#d0d0d0',lw=0.6,zorder=1)
        xs=[0,i,i,ii,ii,a]; ys=[0,0,1,1,2,2]
        ax.plot(xs,[y0+t for t in ys],color=col,lw=2.6,solid_capstyle='round',zorder=3)
        ax.plot([0],[y0],'o',color='#333333',ms=3.5,zorder=4); ax.plot([a],[y0+2],'o',color='#333333',ms=3.5,zorder=4)
        ax.text(-0.6,y0+1,f'$({i},{ii})$',ha='right',va='center',fontsize=9.5)
    ax.set_title(title,fontsize=11.5)
    ax.set_xlim(-3.6,a+0.6); ax.set_ylim(-(len(F)-1)*gap-0.8,2.8); ax.set_aspect('equal'); ax.axis('off')
plt.tight_layout()
plt.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'fig_tworows.png'),dpi=220,bbox_inches='tight')
