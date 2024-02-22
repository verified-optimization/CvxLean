Here, we compare `egg-pre-dcp` with different options (iterative node limits and stop-on-success).

Run this from the root of the repository.

To extract raw data, build `egg-pre-dcp`. Then choose `<dir>` in `scripts/evaluation/data` to store 
the results. I usually give it a date, e.g. `2024_02_17_egg-pre-dcp-options`. Then run the 
following.
```
./scripts/evaluation/egg-pre-dcp-options/run_all.sh <dir>
```
To read all the numerical values, and average them out, and plot the results, run the following.
```
python3 scripts/evaluation/egg-pre-dcp-options/extract_stats.py <dir>
```
