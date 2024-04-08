import sys
import re
import matplotlib.pyplot as plt
import numpy as np
import heapq
import csv

def extract_stats_from_file(file_path):
    with open(file_path, 'r') as file:
        egg_times = []
        command_times = []
        term_sizes = []
        numbers_of_steps = []
        term_jsons = []
        for line in file:
            match = re.search(r'Egg time: (\d+) ms', line)
            if match:
                egg_time = int(match.group(1))
                egg_times.append(egg_time)                
            match = re.search(r'Command time: (\d+) ms', line)
            if match:
                command_time = int(match.group(1))
                command_times.append(command_time)
            match = re.search(r'Term size: (\d+)', line)
            if match:
                term_size = int(match.group(1))
                term_sizes.append(term_size)
            match = re.search(r'Number of steps: (\d+)', line)
            if match:
                number_of_steps = int(match.group(1))
                numbers_of_steps.append(number_of_steps)
            match = re.search(r'Term JSON: (.+)', line)
            if match:
                term_json = match.group(1)
                term_jsons.append(term_json)
        assert len(egg_times) == len(command_times) == len(term_sizes) == len(numbers_of_steps) == len(term_jsons)
        return egg_times, command_times, term_sizes, numbers_of_steps, term_jsons

def plot_stats(fn, xs, xs_label, egg_times, command_times):
    plt.scatter(xs, egg_times, color='orange', label='egg', marker='x')
    plt.scatter(xs, command_times, color='blue', label='command', marker='x')
    plt.xlabel(xs_label)
    plt.ylabel('time (ms)')
    plt.locator_params(axis="both", integer=True, tight=True)
    plt.legend()
    plt.savefig(fn)
    plt.show()

def plot_stats1(fn, xs, xs_label, ys, ys_label):
    plt.scatter(xs, ys, color='black', marker='x')
    plt.xlabel(xs_label)
    plt.ylabel(ys_label)
    plt.locator_params(axis="both", integer=True, tight=True)
    plt.legend()
    plt.savefig(fn)
    plt.show()

eval_dir = './scripts/evaluation/data/' + sys.argv[1]
print(eval_dir)
file_paths = [eval_dir + '/lean_pre_dcp_test_out_{}.txt'.format(i) for i in range(1, 6)]

egg_times = None
command_times = None
term_sizes = None
numbers_of_steps = None
term_jsons = None
for file_path in file_paths:
    stats = extract_stats_from_file(file_path)
    if egg_times is None:
        egg_times = np.array(stats[0])
    else: 
        egg_times += np.array(stats[0])
    if command_times is None:
        command_times = np.array(stats[1])
    else:
        command_times += np.array(stats[1])
    if term_sizes is None:
        term_sizes = np.array(stats[2])
    else:
        term_sizes += np.array(stats[2])
    if numbers_of_steps is None:
        numbers_of_steps = np.array(stats[3])
    else:
        numbers_of_steps += np.array(stats[3])
    if term_jsons is None:
        term_jsons = stats[4]
    else:
        for i in range(len(term_jsons)):
            assert term_jsons[i] == stats[4][i]

    print('Data points:', len(egg_times))

egg_times = egg_times / len(file_paths)
command_times = command_times / len(file_paths)
term_sizes = term_sizes / len(file_paths)
numbers_of_steps = numbers_of_steps / len(file_paths)

# Order matters, this is the order in which tests are run: 
# "Unit", "MainExample", "DGP", "AlmostDGP", "DQCP", "Quiz", "Stanford"
unit_start_idx = 0
unit_count = 113
main_example_start_idx = unit_count
main_example_count = 1
dgp_start_idx = unit_count + main_example_count
dgp_count = 9
adgp_start_idx = unit_count + main_example_count + dgp_count
adgp_count = 4
dqcp_start_idx = unit_count + main_example_count + dgp_count + adgp_count
dqcp_count = 4
quiz_start_idx = unit_count + main_example_count + dgp_count + adgp_count + dqcp_count
quiz_count = 10
stan_start_idx = unit_count + main_example_count + dgp_count + adgp_count + dqcp_count + quiz_count
stan_count = 4 

unit_idxs = [i for i in range(main_example_start_idx,main_example_start_idx+main_example_count)] + [i for i in range(unit_start_idx, unit_start_idx + unit_count)]
quiz_idxs = [i for i in range(quiz_start_idx, quiz_start_idx + quiz_count)]
stan_idxs = [i for i in range(stan_start_idx, stan_start_idx + stan_count)]
dgp_idxs = [i for i in range(dgp_start_idx, dgp_start_idx + dgp_count)] + [i for i in range(adgp_start_idx, adgp_start_idx + adgp_count)]
dqcp_idxs = [i for i in range(dqcp_start_idx, dqcp_start_idx + dqcp_count)]

unit_idxs_len = len(unit_idxs)
print('Unit count:', unit_idxs_len)
quiz_idxs_len = len(quiz_idxs)
print('Quiz count:', quiz_idxs_len)
stan_idxs_len = len(stan_idxs)
print('Stan count:', stan_idxs_len)
dgp_idxs_len = len(dgp_idxs)
print('DGP count:', dgp_idxs_len)
dqcp_idxs_len = len(dqcp_idxs)
print('QCP count:', dqcp_idxs_len)
total_len = unit_idxs_len + quiz_idxs_len + stan_idxs_len + dgp_idxs_len + dqcp_idxs_len

problem_names = [f"unit_{i}" for i in range(1, unit_count + 1)]
problem_names += [f"main_example"]
problem_names += [f"dgp_{i}" for i in range(1, dgp_count + 1)]
problem_names += [f"adgp_{i}" for i in range(1, adgp_count + 1)]
problem_names += [f"dqcp_{i}" for i in range(1, dqcp_count + 1)]
problem_names += [f"quiz_{i}" for i in range(1, quiz_count + 1)]
problem_names += [f"stan_{i}" for i in range(1, stan_count + 1)]

unit_term_sizes = term_sizes[unit_idxs]
quiz_term_sizes = term_sizes[quiz_idxs]
stan_term_sizes = term_sizes[stan_idxs]
dgp_term_sizes = term_sizes[dgp_idxs]
qcp_term_sizes = term_sizes[dqcp_idxs]

unit_min_term_size = np.min(unit_term_sizes)
unit_max_term_size = np.max(unit_term_sizes)
quiz_min_term_size = np.min(quiz_term_sizes)
quiz_max_term_size = np.max(quiz_term_sizes)
stan_min_term_size = np.min(stan_term_sizes)
stan_max_term_size = np.max(stan_term_sizes)
dgp_min_term_size = np.min(dgp_term_sizes)
dgp_max_term_size = np.max(dgp_term_sizes)
qcp_min_term_size = np.min(qcp_term_sizes)
qcp_max_term_size = np.max(qcp_term_sizes)

print('Unit size range:', unit_min_term_size, unit_max_term_size)
print('Quiz size range:', quiz_min_term_size, quiz_max_term_size)
print('Stan size range:', stan_min_term_size, stan_max_term_size)
print('DGP size range:', dgp_min_term_size, dgp_max_term_size)
print('QCP size range:', qcp_min_term_size, qcp_max_term_size)

print('Egg time average: ', np.average(egg_times))
print('Command time average: ', np.average(command_times))
print('Steps average', np.average(numbers_of_steps))
print('Lean time average: ', np.average(command_times - egg_times))
command_times_per_step = np.array([0 if numbers_of_steps[i] == 0 else command_times[i] / numbers_of_steps[i] for i in range(len(command_times))])
print('Average command time per step: ', np.average(command_times_per_step))

results = [(problem_names[i], egg_times[i], command_times[i]) for i in range(len(problem_names))]

output_file = eval_dir + "/pre_dcp_eval_results.csv"

with open(output_file, 'w', newline='') as file:
    writer = csv.writer(file)
    writer.writerow(["problem_name", "egg_time", "command_time"]) 
    writer.writerows(results)

print("Results saved to:", output_file)

# Remove some outliers.
to_remove = 8
idxs_to_remove = heapq.nlargest(to_remove, range(len(command_times)), key=command_times.__getitem__)
for i in range(to_remove):
    idx = idxs_to_remove[i]
    print('Outlier time:', command_times[idx])
    print('Removing outlier: ' + problem_names[idx])

egg_times = np.delete(egg_times, idxs_to_remove)
command_times = np.delete(command_times, idxs_to_remove)
term_sizes = np.delete(term_sizes, idxs_to_remove)
numbers_of_steps = np.delete(numbers_of_steps, idxs_to_remove)

# Remove problems with 0 steps.
idxs_to_remove = [] 
for i in range(len(numbers_of_steps)):
    if numbers_of_steps[i] == 0:
        idxs_to_remove.append(i)
        print('Removing problem with 0 steps: ' + problem_names[i])

egg_times = np.delete(egg_times, idxs_to_remove)
command_times = np.delete(command_times, idxs_to_remove)
term_sizes = np.delete(term_sizes, idxs_to_remove)
numbers_of_steps = np.delete(numbers_of_steps, idxs_to_remove)

lean_times = command_times - egg_times

plot_stats(eval_dir + "/pre_dcp_eval_sizes_time.png", term_sizes, 'term size', egg_times, command_times)
plot_stats(eval_dir + "/pre_dcp_eval_steps_time.png", numbers_of_steps, 'number of steps', egg_times, command_times)
plot_stats1(eval_dir + "/pre_dcp_eval_sizes_steps.png", term_sizes, 'term size', numbers_of_steps, 'number of steps')
