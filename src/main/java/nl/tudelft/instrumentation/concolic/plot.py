import matplotlib.pyplot as plt

# Data: time (in seconds) when each unique error was found for each problem
error_times_data = {
    "Problem 11": [[0,5], [1,8], [2,2], [3,3]],
    "Problem 13": [[0,5], [1,2], [2,4], [3,2], [5,4], [6,2], [8,2], [9,1], [10,1], [18,1]],
    "Problem 14": [[0,1], [1,7], [2,3], [27,3], [28,2], [31,2], [259,1], [278,1]],
    "Problem 15": [[0,2], [1,6], [2,3], [3,5], [4,2], [5,3], [6,3], [8,1], [12,1], [14,1], [16,2], [33,2]],
    "Problem 17": [[0,8], [1,7], [3,3], [4,5], [5,2], [6,4], [7,5], [8,4], [9,1], [11,2], [12,3], [13,1], [14,1], [16,1], [18,1], [24,1], [26,1], [28,1], [35,1], [174,1], [176,1]]
}

plt.figure(figsize=(10, 6))

for problem, data in error_times_data.items():
    times = []
    cumulative_errors = []
    total = 0

    for second, errors_found in data:
        times.append(second)
        total += errors_found
        cumulative_errors.append(total)

    # Extend to 300s by repeating last value
    if times[-1] < 300:
        times.append(300)
        cumulative_errors.append(cumulative_errors[-1])

    plt.step(times, cumulative_errors, where='post', label=problem)

plt.title("Concolic Fuzzer: Unique Errors Over Time (Convergence by Quantity per Second)")
plt.xlabel("Time (s)")
plt.ylabel("Cumulative Unique Errors")
plt.grid(True)
plt.legend()
plt.tight_layout()
plt.xlim(0, 300)
plt.savefig("concolic_convergence_by_rate.png")
plt.show()
