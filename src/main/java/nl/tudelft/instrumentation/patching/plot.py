import os
import pandas as pd
import matplotlib.pyplot as plt

DATA_DIR = "lab_3_fitness"
TIME_LIMIT = 1800  # 30 minutes
INTERVAL = 1  # 1-second intervals for high resolution

plt.figure(figsize=(10, 6))

for filename in os.listdir(DATA_DIR):
    if filename.endswith(".csv"):
        path = os.path.join(DATA_DIR, filename)
        df = pd.read_csv(path)
        times = list(df["Time (s)"])
        fitness = list(df[" Best Fitness"])

        # Extend the last point to the TIME_LIMIT
        times.append(TIME_LIMIT)
        fitness.append(fitness[-1])

        full_time = list(range(0, TIME_LIMIT + 1))
        full_fitness = []

        index = 0
        for t in full_time:
            while index + 1 < len(times) and t >= times[index + 1]:
                index += 1
            full_fitness.append(fitness[index])

        label = os.path.splitext(filename)[0]  # e.g., fitness_over_time_Problem11
        plt.plot(full_time, full_fitness, label=label)

plt.xlabel("Time (s)")
plt.ylabel("Best Fitness")
plt.title("Convergence Plot: Fitness Over Time (Lab 3)")
plt.xlim(0, 1800)
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.savefig("lab3_convergence_plot.png", dpi=300)
plt.show()
