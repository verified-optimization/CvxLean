Here, we compare `egg-pre-dcp` times and `pre_dcp` (Lean) times to calculate the proof replay 
overhead.

Run this from the root of the repository.

To extract raw data, build `CvxLean`. Then choose `<dir>` in `scripts/evaluation/data` to store the 
results. I usually give it a date, e.g. `2024_02_17_lean-pre-dcp`. Then run the following.
```
./scripts/evaluation/lean-pre-dcp/run_all.sh <dir>
```
To read all the numerical values, and average them out, and plot the results, run the following.
```
python3 scripts/evaluation/lean-pre-dcp/extract_stats.py <dir>
```
