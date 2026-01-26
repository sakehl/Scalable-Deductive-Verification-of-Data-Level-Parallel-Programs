This contains everything to run the experiments and verify the Lean proof of the paper 'Scalable Deductive Verification of Data-Level Parallel Programs'

# VerCors
In the `VerCors` folder contains the VerCors version used for this paper. read the `VerCor/README.md` for dependencies. If Java 17 and `clang` is installed, probably everything builds correctly by executing `VerCors/bin/vct --version`.

# Lean proof of Section 3
The lean proof can be found in the folder `LeanProof`. See the Appendix on how to translate the proof concepts to the paper concepts. Section 3 also contains a proof sketch, to help further understand the structure of the proof.

# Experiments
The experiments of Section 5, can be found under `Experiments`. Read the respective `README.md` in each folder for details. Mostly the experiments can be run by using the scripts `Experiments/ClBlast/run_experiments.py` and `Experiments/HaliVerExperiments/run_experiments.py`. The resulting tables and figures can be recreated using the `xml_to_latex.py` scripts.