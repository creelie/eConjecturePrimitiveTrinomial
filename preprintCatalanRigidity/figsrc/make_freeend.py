import os
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
plt.rcParams.update({'font.family':'serif','mathtext.fontset':'cm','font.size':11})
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'fig_freeend.png')

F = ['1010101','1010110','1011001','1011010','1110101','1111001','1110111','1111011']
m = 7

def common(x, y):
    c = wx = wy = 0
    for s, t in zip(x, y):
        if s == t and wx == wy:
            c += 1
        wx += s == '1'; wy += t == '1'
    return c

C = [[common(x, y) for y in F] for x in F]
assert all(C[i][j] % 2 == 1 for i in range(8) for j in range(8) if i != j)
cols = {4:'#1f4e9c', 5:'#2a7f3f', 6:'#b0172f'}

fig = plt.figure(figsize=(13, 5.6))
gs = GridSpec(2, 6, figure=fig, width_ratios=[1,1,1,1,0.25,2.3], wspace=0.15, hspace=0.25)
for k, w in enumerate(F):
    ax = fig.add_subplot(gs[k // 4, k % 4])
    for i in range(m + 1):
        for j in range(m + 1 - i):
            if i + j < m:
                ax.plot([i, i + 1], [j, j], color='#d4d4d4', lw=0.6, zorder=1)
                ax.plot([i, i], [j, j + 1], color='#d4d4d4', lw=0.6, zorder=1)
    ax.plot([0, m], [m, 0], ls='--', color='#888888', lw=0.8, zorder=1)
    x = y = 0; xs = [0]; ys = [0]
    for s in w:
        if s == '1': y += 1
        else: x += 1
        xs.append(x); ys.append(y)
    b = w.count('1')
    ax.plot(xs, ys, color=cols[b], lw=2.6, solid_capstyle='round', zorder=3)
    ax.plot([0], [0], 'o', color='#333333', ms=3, zorder=4)
    ax.plot([xs[-1]], [ys[-1]], 'o', color=cols[b], ms=5.5, zorder=4)
    ax.set_title(f'$P_{k+1}$ to $({m-b},{b})$', fontsize=10.5)
    ax.set_xlim(-0.4, m + 0.4); ax.set_ylim(-0.4, m + 0.4); ax.set_aspect('equal'); ax.axis('off')
ax = fig.add_subplot(gs[:, 5])
ax.imshow([[1 if i == j else (0.55 if C[i][j] >= 3 else 0.18) for j in range(8)] for i in range(8)],
          cmap='Greys', vmin=0, vmax=1.6)
for i in range(8):
    for j in range(8):
        ax.text(j, i, str(C[i][j]), ha='center', va='center', fontsize=11,
                color='white' if i == j else '#111111')
ax.set_xticks(range(8)); ax.set_yticks(range(8))
ax.set_xticklabels([f'$P_{k+1}$' for k in range(8)]); ax.set_yticklabels([f'$P_{k+1}$' for k in range(8)])
ax.tick_params(length=0)
ax.set_title('shared edges $|E(P_i)\\cap E(P_j)|$', fontsize=11)
plt.savefig(OUT, dpi=220, bbox_inches='tight')
