# Experiments
These contain the verification of the kernels of CLBlast.
The kernels were taken from:
https://github.com/CNugteren/CLBlast/tree/2bec4b20d832fa606cdb7ba096da5301492ff0c5/src/kernels/level1
and we added verification conditions towards them such that they can be verified with VerCors.
## Run experiments
Use 
```
python3 run_experiments.py --repetition 10 --timeout 3600 --timestamp 2026-01-12
```

The experiments take several days to run, mostly because of the timeout of 3600s and the repetitions of 10. This timeout is needed mostly level 2 kernels.
But setting this to for example 200s makes things a lot faster and will still make most examples verify.

**Note**: the speedup calculated considers the timeouts. Thus setting a lower timeout can report lower speedups.

The timestamp can be any string, it is how the output results are named: i.e. `results\exp-2026-01-12.xml`.
We include our original results with time stamp `2026-01-12`. 
The script skips results which are already present, so to rerun give your own timestamp.

## View experiments
The experiments are stored in the subfolder `results`.

Use 
```
python3 -m http.server
```
To start a http server to view the results at
```
results/exp-2026-01-12.xml
```
## Make table
```
python3 xml_to_latex.py --timestamp 2026-01-12
```
This generates a table and parblot using latex at `results/table.pdf`.