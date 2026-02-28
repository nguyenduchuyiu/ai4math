# Re-run a faster version with reduced epochs and smaller network so it completes within the execution time limit.
# This will train fewer epochs and produce an animation with snapshots saved every few epochs.
import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from IPython.display import HTML

# DATA
N = 2000
t_numpy = np.linspace(0.0, 4.0 * np.pi, N).astype(np.float32)
r = 0.1 * t_numpy
x_numpy = r * np.cos(t_numpy)
y_numpy = r * np.sin(t_numpy)
z_numpy = 0.2 * t_numpy
xyz_gt = np.stack([x_numpy, y_numpy, z_numpy], axis=1).astype(np.float32)

t_tensor = torch.from_numpy(t_numpy).unsqueeze(1)
xyz_gt_tensor = torch.from_numpy(xyz_gt)

# MODEL (smaller)
class Parametric3DNetSmall(nn.Module):
    def __init__(self, hidden=64):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(1, hidden),
            nn.Tanh(),
            nn.Linear(hidden, hidden),
            nn.Tanh(),
            nn.Linear(hidden, 3)
        )
    def forward(self, t):
        return self.net(t)

model = Parametric3DNetSmall(hidden=64)

# TRAIN (smaller)
device = torch.device("cpu")
model.to(device)
t_tensor = t_tensor.to(device)
xyz_gt_tensor = xyz_gt_tensor.to(device)

optimizer = torch.optim.Adam(model.parameters(), lr=5e-4)
loss_func = nn.MSELoss()

epochs = 4000
snapshot_interval = 10
history = []

print("Training (short run)...")
for epoch in range(epochs):
    pred = model(t_tensor)
    loss = loss_func(pred, xyz_gt_tensor)
    optimizer.zero_grad()
    loss.backward()
    optimizer.step()
    if epoch % snapshot_interval == 0:
        history.append((epoch, loss.item(), pred.detach().cpu().numpy()))
print("Done. Collected", len(history), "snapshots.")

# ANIMATION 3D
fig = plt.figure(figsize=(7,7))
ax = fig.add_subplot(projection='3d')

ax.plot(x_numpy, y_numpy, z_numpy, linestyle='--', linewidth=1.5, label='Ground truth')
pred_line, = ax.plot([], [], [], linewidth=2, label='Prediction')

ax.set_box_aspect([1,1,1])
ax.set_xlabel('x')
ax.set_ylabel('y')
ax.set_zlabel('z')
ax.legend()

title_text = ax.text2D(0.5, 0.95, "", transform=ax.transAxes, ha='center')

def init():
    pred_line.set_data([], [])
    pred_line.set_3d_properties([])
    title_text.set_text("")
    return pred_line, title_text

def update(i):
    epoch, loss_val, pred_np = history[i]
    x_pred = pred_np[:,0]
    y_pred = pred_np[:,1]
    z_pred = pred_np[:,2]
    pred_line.set_data(x_pred, y_pred)
    pred_line.set_3d_properties(z_pred)
    title_text.set_text(f"Epoch {epoch}  loss={loss_val:.6f}")
    return pred_line, title_text

anim = FuncAnimation(fig, update, frames=len(history), init_func=init, interval=60, blit=True, repeat=False)

plt.show()

