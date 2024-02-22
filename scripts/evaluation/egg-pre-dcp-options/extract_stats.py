import sys
import re

def extract_test_results(file_path):
    test_results = {}

    with open(file_path, 'r') as file:
        data = file.read()

        # Define regex patterns.
        test_name_pattern = r'test_(\w+)::(\w+)'
        total_time_pattern = r'Total time: (\d+) ms\.'
        e_graph_time_pattern = r'E-graph building time: (\d+) ms\.'
        step_extraction_time_pattern = r'Step extraction time: (\d+) ms\.'
        num_of_nodes_pattern = r'Succeeded with node limit (\d+) \(using (\d+) nodes\).'
        num_steps_pattern = r'Number of steps: (\d+)\.'
        best_term_size_pattern = r'Best term size: (\d+)\.'
        best_num_variables_pattern = r'Best number of variables: (\d+)\.'

        failure_pattern = r'failures:(.*?)test_(\w+)'

        # Extract test names and corresponding total times or failure status.
        test_names = re.findall(test_name_pattern, data)
        test_names = [x[1] for x in test_names]
        total_times = re.findall(total_time_pattern, data)
        e_graph_times = re.findall(e_graph_time_pattern, data)
        step_extraction_times = re.findall(step_extraction_time_pattern, data)
        num_of_nodes = re.findall(num_of_nodes_pattern, data)
        num_of_nodes = [int(x[1]) for x in num_of_nodes]
        num_steps = re.findall(num_steps_pattern, data)
        best_term_sizes = re.findall(best_term_size_pattern, data)
        best_num_variables = re.findall(best_num_variables_pattern, data)

        failures = re.findall(failure_pattern, data, re.DOTALL)
        failed_tests = ["test_" + test[1] for test in failures]

        print(num_of_nodes)
        print(len(test_names), len(total_times))
        assert len(test_names) == len(total_times) + len(failed_tests)
        assert len(total_times) == len(e_graph_times)
        assert len(total_times) == len(step_extraction_times)
        assert len(total_times) == len(num_of_nodes)
        assert len(total_times) == len(num_steps)
        assert len(total_times) == len(best_term_sizes)
        assert len(total_times) == len(best_num_variables)

        # Match test names with their total times or failure status.
        i = 0
        for test_name in test_names:
            if test_name in failed_tests:
                test_results[test_name] = {
                    'total_time': None, 
                    'e_graph_time': None, 
                    'step_extraction_time': None,
                    'num_of_nodes': None,
                    'steps': None,
                    'term_size': None,
                    'num_variables': None
                }
            else:
                test_results[test_name] = {
                    'total_time': int(total_times[i]),
                    'e_graph_time': int(e_graph_times[i]),
                    'step_extraction_time': int(step_extraction_times[i]),
                    'num_of_nodes': num_of_nodes[i],
                    'steps': int(num_steps[i]),
                    'term_size': int(best_term_sizes[i]),
                    'num_variables': int(best_num_variables[i])
                }
                i += 1

    return test_results

# Change this to the path where the result of `run_all.sh` is.
data_path = 'scripts/evaluation/data/' + sys.argv[1] + '/'

files = {
    "stop" : "stop_on_success.txt",
    "iter" : "iterative.txt",
}

results = {}

for key, value in files.items():
    file_path = data_path + value
    results[key] = extract_test_results(file_path)

benchmark_path = 'scripts/evaluation/egg-pre-dcp-options/benchmark.txt'
benchmark = []
with open(benchmark_path, 'r') as file:
    benchmark = file.readlines()

print("---- Table with key results on stop and iter ----")
with open(data_path + 'summary.csv', 'w') as file:
    for prob in benchmark:
        prob = "test_" + prob.strip()
        prob_results_stop = results["stop"][prob]
        prob_results_iter = results["iter"][prob]
        if prob_results_iter["steps"] < 1 or prob_results_stop["steps"] < 1:
            continue
        # Problem & Time (stop) & Steps (stop) & Term size (stop) & Time (iter) & Steps (iter) & Term size (iter)
        values = [prob[5:]]
        values += ["-" if prob_results_stop["total_time"] is None else str(prob_results_stop["total_time"]) + " ms"]
        values += ["-" if prob_results_stop["steps"] is None else str(prob_results_stop["steps"])]
        values += ["-" if prob_results_stop["term_size"] is None else str(prob_results_stop["term_size"])]
        values += ["-" if prob_results_iter["total_time"] is None else str(prob_results_iter["total_time"]) + " ms"]
        values += ["-" if prob_results_iter["steps"] is None else str(prob_results_iter["steps"])]
        values += ["-" if prob_results_iter["term_size"] is None else str(prob_results_iter["term_size"])]
        file.write(','.join(values) + '\n')
        # To copy-paste into LaTeX.
        print(' & '.join(values) + ' \\\\')
        print('\\hline')

for key, _ in files.items():
    print("----- " + key + " -----")
    with open(data_path + key + '_summary.csv', 'w') as file:
        for prob in benchmark:
            prob = "test_" + prob.strip()
            prob_results = results[key][prob]
            if prob_results["steps"] < 1:
                continue
            # Problem & Time & Build time & Extraction time & Number of nodes & Steps & Term size 
            values = [prob[5:]]
            values += ["-" if prob_results["total_time"] is None else str(prob_results["total_time"]) + " ms"]
            values += ["-" if prob_results["e_graph_time"] is None else str(prob_results["e_graph_time"]) + " ms"]
            values += ["-" if prob_results["step_extraction_time"] is None else str(prob_results["step_extraction_time"]) + " ms"]
            values += ["-" if prob_results["num_of_nodes"] is None else str(prob_results["num_of_nodes"])]
            values += ["-" if prob_results["steps"] is None else str(prob_results["steps"])]
            values += ["-" if prob_results["term_size"] is None else str(prob_results["term_size"])]
            file.write(','.join(values) + '\n')
            # To copy-paste into LaTeX.
            print(' & '.join(values) + ' \\\\')
            print('\\hline')
