import argparse
from typing import List, Tuple
import xml.etree.ElementTree as ET
import subprocess
import re
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

DIR = os.path.dirname(os.path.abspath(__file__))

def parse_xml_exp(input_xml):
    tree = ET.parse(input_xml)
    root = tree.getroot()
    experiments = {}
    experiments_mem = {}

    for group in root.findall('group'):
        i = group.find('i').text

        for file in group.findall('file'):
            name = file.find('name').text
            file_info = {
                'name': name,
                'return_code': file.find('return_code').text,
                'elapsed_time': round(float(file.find('elapsed_time').text)),
                'backend_duration': extract_backend_duration(file.find('stdout').text)
            }
            base_name = get_base_filename_exp(name)
            tags = get_tags_exp(name)
            if("mem" in name):
                res_map = experiments_mem
            else:
                res_map = experiments
            

            if base_name not in res_map:
                res_map[base_name] = {}
            if tags not in res_map[base_name]:
                res_map[base_name][tags] = []
            res_map[base_name][tags].append(file_info)

    return experiments, experiments_mem

def extract_backend_duration(stdout):
    match = re.search(r"Done: BackendVerification \(at [^,]+, duration: (\d+):(\d+):(\d+)\)", stdout)
    if match:
        hours, minutes, seconds = map(int, match.groups())
        return hours * 3600 + minutes * 60 + seconds
    return None

def get_base_filename_exp(name):
    if "_non_unique" in name:
        name = name.replace("_non_unique", "")
    if "_mem" in name:
        name = name.replace("_mem", "")
    if name.endswith(".c"):
        name = name[:-2]
    return name

def get_tags_exp(name):
    result = ""
    if "_non_unique" in name:
        result = result + "Normal"
    else:
        result = result + "Unique"
    return result

def neutral(color: bool)-> str:
    return ""

def green(color: bool)-> str:
    return "\\cellcolor{ForestGreen!25}" if color else ""

def red(color: bool)-> str:
    return "\\cellcolor{BrickRed!25}" if color else ""

def color_result_line(res_nr, n_unique, avr_t_unique, avr_v_unique, n_normal, avr_t_normal, avr_v_normal)->str:
    unique_empty = n_unique == 0
    normal_empty = n_normal == 0
    current_line = ""

    if res_nr == 0:  # Only color cells for return code 0
        current_line += f"& {green(not normal_empty and unique_empty)}{red(normal_empty)} {n_normal}"

        color_normal_v = not normal_empty and (unique_empty or avr_v_normal < avr_v_unique)
        current_line += f"& {avr_t_normal} & {neutral(color_normal_v)} {avr_v_normal}"

        current_line += f"& {green(not unique_empty and normal_empty)}{red(unique_empty)} {n_unique}"

        color_unique_v = not unique_empty and (normal_empty or avr_v_unique < avr_v_normal)
        current_line += f"& {avr_t_unique} & {neutral(color_unique_v)} {avr_v_unique}"
        
        

        if(not normal_empty and not unique_empty and not avr_v_unique == "" and not avr_v_normal == ""):
            speedup = round(avr_v_normal/avr_v_unique, 1)
            current_line += f"& {green(speedup > 1)}{red(speedup < 1)} {speedup}"
        else:
            current_line += "& "
    elif res_nr ==3:
        # For timeout we print no time
        if(n_normal > 0):
            current_line += f"& {n_normal} & - & -"
        else :
            current_line += f"& 0 &  & "
        if(n_unique > 0):
            current_line += f"& {n_unique} & - & -"
        else :
            current_line += f"& 0 &  & "
    else:
        current_line += f"& {n_normal} & {avr_t_normal} & {avr_v_normal}"
        current_line += f"& {n_unique} & {avr_t_unique} & {avr_v_unique}"
    
    return current_line


def color_results(res_nr, n_normal, avr_v_normal, other_results: List[Tuple[int, float, float]])->str:
    normal_empty = n_normal == 0
    current_line = ""

    
    if res_nr == 0:  # Always give nr of succesfull verification and color them
        current_line += f"& {red(normal_empty)} {n_normal}"
        current_line += f" & {avr_v_normal}"

        results = [x[1] for x in other_results if x[1] != ""]
        best_result = min(results) if results else ""
        for n, avr_v, speedup_total in other_results:
            is_empty = n == 0
            if n == -1:
                current_line += "& - & - & "
            else:
                color_red = red(avr_v_normal<avr_v) if not is_empty and not normal_empty else ""
                current_line += f"& {green(not is_empty and normal_empty)}{red(is_empty)} {n}"
                current_line += f"& {green(best_result==avr_v)}{color_red} {avr_v}"
                current_line += f"& {speedup_total}"
            # if not is_empty and not normal_empty:
            #     speedup = round(avr_v_normal/avr_v, 2)
            #     current_line += f"& {speedup} ({speedup_total})" #{green(speedup > 1)}{red(speedup < 1)} {speedup}"
            # else:
            #     current_line += f"& - ({speedup_total})"
    else:
        if(res_nr ==3):
            if(n_normal > 0):
                avr_v_normal = "-"
            else:
                avr_v_normal = ""
        current_line += f"& {n_normal} & {avr_v_normal}"
        for n, avr_v, _ in other_results:
            if(res_nr ==3):
                if(n > 0):
                    avr_v = "-"
                else:
                    avr_v = ""
            current_line += f"& {n} & {avr_v} &"
    
    return current_line

def generate_latex_tabular_exp(experiments, is_mem: bool=False):
    latex = []
    result_name = {0: "\\checkmark", 1: "$\\times$", 2: "Error", 3: "T.O."}

    latex.append("\\begin{tabular}{lll|rrr|rrr|r}")
    latex.append("\\hline")
    latex.append(" & & & \\multicolumn{3}{c|}{\\textbf{Base}} & \\multicolumn{3}{c|}{\\textbf{Unique}} & \\\\")
    latex.append("\\textbf{Name} & \\textbf{V} & \\textbf{Result} & \\textbf{\\#} & \\textbf{T$_t$} & " +
      "\\textbf{T} & \\textbf{\\#} & \\textbf{T$_t$} & \\textbf{T} & \\textbf{Speedup} \\\\")
    latex.append("\\hline")

    total_normal = 0
    total_unique = 0
    total_v_normal = 0
    total_v_unique = 0
    for base_name, tags in experiments.items():
        base_name = base_name.replace("_", "\_")
        if(base_name[-1] in ["0", "1", "2", "3"]):
            version = base_name[-1]
            base_name = base_name[:-2]
        else:
            version = ""
        def get_avr(xs):
            return round(sum(xs)/len(xs)) if xs else ""
        
        unique_runs = tags["Unique"]
        normal_runs = tags["Normal"]
        prev_base_name = ""
        tag_printed = False
        rest_conv_printed = True
        if version == "":
          if(base_name == "depthwise\_separable\_conv"):
            first_line = "\\multicolumn{2}{l}{depthwise\_}"
            second_line = "\\multicolumn{2}{l}{separable\_conv}"
          else:
            first_line = f"\\multicolumn{{2}}{{l}}{{{base_name}}}"
        elif version == "0":
          first_line = f"{base_name} & {version}"
        else:
          first_line = f" & {version}"
        for i in range(0, 4):
            if(base_name == "depthwise\_separable\_conv"):
                if not tag_printed:
                    current_line = first_line
                    rest_conv_printed = False
                if tag_printed and not rest_conv_printed:
                    current_line = second_line
            else:
                current_line = first_line if not tag_printed else "& "
            current_line += f"& {result_name[i]}"
            times_t_unique = [run.get('elapsed_time') for run in unique_runs if run.get('return_code') == str(i)]
            times_t_normal = [run.get('elapsed_time') for run in normal_runs if run.get('return_code') == str(i)]
            times_v_unique = [run.get('backend_duration') for run in unique_runs if run.get('return_code') == str(i)]
            times_v_normal = [run.get('backend_duration') for run in normal_runs if run.get('return_code') == str(i)]
            
            avr_t_unique = get_avr(times_t_unique)
            avr_t_normal = get_avr(times_t_normal)
            avr_v_unique = get_avr(times_v_unique)
            avr_v_normal = get_avr(times_v_normal)
            current_line += color_result_line(i, len(times_t_unique), avr_t_unique, avr_v_unique,
                                                 len(times_t_normal), avr_t_normal, avr_v_normal)
            if i == 0 and len(times_t_unique)>0 and len(times_t_normal)>0:
                total_normal += avr_t_normal
                total_v_normal += avr_v_normal
                total_unique += avr_t_unique
                total_v_unique += avr_v_unique

            if len(times_t_unique) > 0 or len(times_t_normal) > 0:
                latex.append(current_line + " \\\\")
                if tag_printed:
                    rest_conv_printed = True
                tag_printed = True
            elif i == 3 and not rest_conv_printed:
                latex.append("separable\_conv & & & & & & & & \\\\")
        # if(prev_base_name != base_name[:-2] and (version =="" or version == "3")):
        if(prev_base_name != base_name[:-2]):
            latex.append("\\hline")
        prev_base_name = base_name[:-2]
    speedup = round(total_v_normal/total_v_unique, 1)
    latex.append("\\hline")
    latex.append(f"Total & & \\checkmark & & {total_normal} & {total_v_normal} & & {total_unique} & {total_v_unique} & {green(speedup > 1)}{red(speedup < 1)} {speedup}  \\\\")
    latex.append("\\hline")
    latex.append("\\end{tabular}")
    print(f"Total normal: {total_normal}, total unique: {total_unique}, mem:{is_mem}")
    return latex

def parse_xml(input_xml):
    tree = ET.parse(input_xml)
    root = tree.getroot()
    experiments = {}

    for group in root.findall('group'):
        i = group.find('i').text

        for file in group.findall('file'):
            name = file.find('name').text
            tags = group.find('tags').text
            file_info = {
                'name': name,
                'return_code': file.find('return_code').text,
                'elapsed_time': round(float(file.find('elapsed_time').text)),
                'backend_duration': extract_backend_duration(file.find('stdout').text)
            }
            base_name = get_base_filename(name)
            # tags = get_tags(name)
            if base_name not in experiments:
                experiments[base_name] = {}
            if tags not in experiments[base_name]:
                experiments[base_name][tags] = []
            experiments[base_name][tags].append(file_info)

    return experiments

def get_base_filename(name):
    name = name.replace("_non_unique", "")
    name = name.replace("CB", "")
    name = name.replace("level1/","").replace("level2/","")
    if name.endswith(".c"):
        name = name[:-2]
    if name.endswith(".cl"):
        name = name[:-3]
    return name

def get_tags(name):
    result = ""
    if "_non_unique" in name:
        result = result + "Normal"
    else:
        result = result + "Unique"
    if "CB" in name:
        result = result + "-CB"
    else:
        result = result + "-NCB"
    return result

def generate_latex_padre(experiments):
    names = {"StepHalide": "\\texttt{step}",
              "SubDirectionHalide": "\\texttt{sub\\_direction}",
                "SolveDirectionHalide": "\\texttt{solve\\_direction}",
                  "PerformIterationHalide": "\\texttt{perform\\_iteration}"}
    latex = []
    i = 0
    result_name = {0: "\\checkmark", 1: "$\\times$", 2: "Error", 3: "T.O."}
    latex.append("\\newcommand{\widthPadre}{0.7}")
    for base_name, tags in experiments.items():
        latex.append("\\subfloat[\\label{tab:" + base_name + "}\\texttt{" + names[base_name] +"}]{")
        latex.append("\\resizebox{\\widthPadre\\textwidth}{!}{")
        latex.append("\\begin{tabular}{ll|rrr|rrr|r}")
        latex.append("\\hline")
        latex.append(" & & \\multicolumn{3}{c|}{\\textbf{Base}} & \\multicolumn{3}{c}{\\textbf{Unique}} & \\\\")
        latex.append("\\textbf{Version} & \\textbf{Result} & \\textbf{\\#} & \\textbf{T$_t$} & \\textbf{T}"+ 
                     " & \\textbf{\\#} & \\textbf{T$_t$} & \\textbf{T} & \\textbf{Speedup} \\\\")
        latex.append("\\hline")

        def get_avr(xs):
            return round(sum(xs)/len(xs)) if xs else ""
        
        for tag in ["CB", "NCB"]:
            unique_runs = tags["Unique-" + tag]
            normal_runs = tags["Normal-" + tag]
            tag_printed = False
            for i in range(0, 4):
                current_line = f"{tag}" if not tag_printed else ""
                current_line += f"& {result_name[i]}"
                times_t_unique = [run.get('elapsed_time') for run in unique_runs if run.get('return_code') == str(i)]
                times_t_normal = [run.get('elapsed_time') for run in normal_runs if run.get('return_code') == str(i)]
                times_v_unique = [run.get('backend_duration') for run in unique_runs if run.get('return_code') == str(i)]
                times_v_normal = [run.get('backend_duration') for run in normal_runs if run.get('return_code') == str(i)]
                
                avr_t_unique = get_avr(times_t_unique)
                avr_t_normal = get_avr(times_t_normal)
                avr_v_unique = get_avr(times_v_unique)
                avr_v_normal = get_avr(times_v_normal)
                
                current_line += color_result_line(i, len(times_t_unique), avr_t_unique, 
                                                  avr_v_unique, len(times_t_normal), avr_t_normal, avr_v_normal)

                if len(times_t_unique) > 0 or len(times_t_normal) > 0:
                    latex.append(current_line + " \\\\")
                    tag_printed = True
                
            latex.append("\\hline")
        latex.append("\\end{tabular}")
        latex.append("}")
        latex.append("}")
        latex.append("\\\\")
    
    return "\n".join(latex)

def read_functional_correct(filename):
    with open(filename, 'r') as f:
        return set(line.strip() for line in f if line.strip())

def read_nr_arrays(filename):
    """Read CSV file with kernel name and array counts."""
    import csv
    nr_arrays = {}
    with open(filename, 'r') as f:
        reader = csv.reader(f)
        for row in reader:
            if len(row) >= 4:  # Ensure we have at least 4 columns
                kernel_name = row[0]
                const_arrays = row[1]
                arrays = row[2]
                annotations = row[3]
                nr_arrays[kernel_name] = (const_arrays, arrays, annotations)
    return nr_arrays

def generate_latex_blas(experiments, level):
    # names = {"StepHalide": "\\texttt{step}",
    #           "SubDirectionHalide": "\\texttt{sub\\_direction}",
    #             "SolveDirectionHalide": "\\texttt{solve\\_direction}",
    #               "PerformIterationHalide": "\\texttt{perform\\_iteration}"}
    latex = []
    labels = ['normal', 'unique', 'const', 'extract', 'unique-const-extract']
    names = {'unique': 'Unique', 'const': 'Immutable', 'extract': 'Extract', 'unique-const-extract' : 'All'}
    i = 0
    result_name = {0: "\\checkmark", 1: "$\\times$", 2: "Error", 3: "T.O."}
    if(level == 1): 
        latex.append("\\newcommand{\\widthPadre}{0.9}")
    latex.append("\\subfloat[\\label{tab:blaslevel" + str(level) + "}\\texttt{CLBLAS level " + str(level) + " kernels}]{")
    latex.append("\\resizebox{\\widthPadre\\textwidth}{!}{")
    
    
    tab = "\\begin{tabular}{l|lll|l|rr"
    for l in labels[1:]:
        tab += "|rr S[table-format=-4.1]"
    tab += "r}"
    latex.append(tab)
    latex.append("\\hline")
    head = " & & & & & \\multicolumn{2}{c|}{\\textbf{Base}}"
    for l in labels[1:]:
        head += "& \\multicolumn{3}{c}{\\textbf{" + names[l] +"}}"
    head += "\\\\"
    latex.append(head)
    latex.append("\\textbf{Kernel} & $\#_{imm}$ & $\#_{p}$ & $\#_{A}$ & \\textbf{Result} & \\textbf{\\#} & \\textbf{T}"+ 
                    "".join(" & \\textbf{\\#} & \\textbf{T} & \\textbf{Speedup}" for _ in labels[1:])
                + "\\\\"
                )
    latex.append("\\hline")
    functional_correct = read_functional_correct("functionalcorrect.txt")
    nr_arrays = read_nr_arrays("nr_arrays.csv")

    totals = {}
    totals_normal = {}
    for l in labels:
        totals[l] = 0
        totals_normal[l] = 0

    for base_name, tags in experiments.items():
        original_name = get_base_filename(base_name)
        info = nr_arrays.get(original_name, ("-", "-", "-"))
        if original_name in functional_correct:
            name = original_name + "$^\dagger$"
        else:
            name = original_name
        

        def get_avr(xs):
            xs = [x for x in xs if x is not None]
            return round(sum(xs)/len(xs)) if xs and len(xs) > 0 else ""
        
        normal_runs = tags["normal"]
        avr_normal = get_avr([run.get('backend_duration') for run in normal_runs])
        totals['normal'] += avr_normal
        
        
        tag_printed = False
        for i in range(0, 4):
            current_line = f"{name} & {info[0]} & {info[1]} & {info[2]} " if not tag_printed else " & & &"
            current_line += f"& {result_name[i]}"
            # times_t_normal = [run.get('elapsed_time') for run in normal_runs if run.get('return_code') == str(i)]
            times_v_normal = [run.get('backend_duration') for run in normal_runs if run.get('return_code') == str(i)]
            # avr_t_normal = get_avr(times_t_normal)
            avr_v_normal = get_avr(times_v_normal)

            color_results_list = []
            pos_len = False
            for l in labels[1:]:
                runs_l = tags[l]
                avr_total = get_avr([run.get('backend_duration') for run in runs_l])
                speedup_total = round(avr_normal/avr_total, 1) if avr_total != "" and avr_normal != "" and avr_total !=0 else ""
                times_v_l = [run.get('backend_duration') for run in runs_l if run.get('return_code') == str(i)]
                avr_v_l = get_avr(times_v_l)
                if original_name == 'xswap' and l == 'const' or original_name == 'xscal' and (l == 'const' or l == 'unique' or l == 'unique-const-extract'):
                    color_results_list.append( (-1, "", "") )
                else:
                    color_results_list.append( (len(times_v_l), avr_v_l, speedup_total) )
                    if i == 0:
                        totals[l] += avr_total
                        totals_normal[l] += avr_normal
                if len(times_v_l) > 0:
                    pos_len = True
                
                    
            current_line += color_results(i, len(times_v_normal), avr_v_normal, color_results_list)

            

            if pos_len or len(times_v_normal) > 0:
                latex.append(current_line + " \\\\")
                tag_printed = True
                latex.append("\\hline")

    speedups = []
    for l in labels[1:]:
        speedup = round(totals_normal[l]/totals[l], 1) if totals[l] !=0 else ""
        speedups.append(speedup)
    
    latex.append("\\hline")
    latex.append(f"Total & & & & & & {totals[labels[0]]} & & {totals[labels[1]]} & {speedups[0]} & & {totals[labels[2]]} & {speedups[1]} & & {totals[labels[3]]} & {speedups[2]} & & {totals[labels[4]]} & {speedups[3]}  \\\\")
    latex.append("\\hline")
    # latex.append("\\hline")
            
    latex.append("\\end{tabular}")
    latex.append("}")
    latex.append("}")
    latex.append("\\\\")
    
    return "\n".join(latex)

def generate_blas_barplots(experiments, level: int):
    labels = ['normal', 'unique', 'const', 'extract', 'unique-const-extract']
    names = {'normal': 'Base', 'unique': 'Unique', 'const': 'Immutable',
             'extract': 'Extract', 'unique-const-extract': 'All'}
    colors = {'normal': '#4C72B0', 'unique': '#55A868', 'const': '#C44E52',
              'extract': '#8172B2', 'unique-const-extract': '#64B5CD'}

    def stats(runs):
        vals = [r.get("backend_duration") for r in runs
                if r.get("return_code") >= "0" and r.get("backend_duration") is not None]
        if not vals:
            return None, None
        return np.mean(vals), np.std(vals, ddof=1) 
    
    def count_success(runs):
        return len([r for r in runs if r.get("return_code") == "0"])

    kernels = []
    kernel_positions = []
    variant_means = {v: [] for v in labels}
    variant_errs = {v: [] for v in labels}
    variant_positions = {v: [] for v in labels}
    variant_success = {v: [] for v in labels}  # Store success counts per kernel per variant
    base_absolutes = []  # Store absolute base times for labels
    
    # Track totals for the total bar
    variant_totals = {v: 0.0 for v in labels}
    variant_variances = {v: 0.0 for v in labels}

    bar_width = 0.12
    group_gap = 0.22
    functional_correct = read_functional_correct("functionalcorrect.txt")

    for idx, kernel in enumerate(sorted(experiments.keys())):
        base_mean, base_std = stats(experiments[kernel].get('normal', []))
        if base_mean is None or base_mean == 0:
            continue  # cannot normalize without a valid base
        group_start = idx * ((len(labels) * bar_width) + group_gap)
        kernel_positions.append(group_start + (len(labels) - 1) * bar_width / 2)
        original_name = get_base_filename(kernel)
        if original_name in functional_correct:
            name = original_name + "$^\dagger$"
        else:
            name = original_name
        kernels.append(name)
        
        

        base_absolutes.append(base_mean)

        for j, variant in enumerate(labels):
            if kernel == "xswap" and variant == "const" or kernel == "xscal" and variant in ["const", "unique"]:
                # These kernels are same as base, so get that timing for totals
                runs = experiments[kernel].get('normal', [])
                mean, std = stats(runs)
                variant_totals[variant] += mean
                variant_variances[variant] += std**2
                continue
            if kernel == "xscal" and variant == "unique-const-extract":
                # Get the extract version
                runs = experiments[kernel].get('extract', [])
                mean, std = stats(runs)
                variant_totals[variant] += mean
                variant_variances[variant] += std**2
                continue

            runs = experiments[kernel].get(variant, [])
            mean, std = stats(runs)
            success_count = count_success(runs)
            if mean is None:
                mean_rel, std_rel = np.nan, 0.0
            else:
                mean_rel = 100.0 * mean / base_mean
                std_rel = 100.0 * std / base_mean / np.sqrt(10)
                # Accumulate absolute times for total bar
                variant_totals[variant] += mean
                variant_variances[variant] += std**2
            x = group_start + j * bar_width
            variant_means[variant].append(mean_rel)
            variant_errs[variant].append(std_rel)
            variant_positions[variant].append(x)
            variant_success[variant].append(success_count)

    if not kernels:
        return
    
    # Add total bar group at the end
    total_idx = len(kernels)
    total_group_start = total_idx * ((len(labels) * bar_width) + group_gap)
    kernel_positions.append(total_group_start + (len(labels) - 1) * bar_width / 2)
    kernels.append("Total")
    
    # Calculate total bar values
    base_total = variant_totals['normal']
    base_absolutes.append(base_total)
    
    for j, variant in enumerate(labels):
        if variant_totals[variant] > 0 and base_total > 0:
            # Calculate relative percentage for total
            total_rel = 100.0 * variant_totals[variant] / base_total
            x = total_group_start + j * bar_width
            errs_rel = 100.0 * variant_variances[variant]**0.5 / base_total / np.sqrt(10)
            variant_means[variant].append(total_rel)
            variant_errs[variant].append(errs_rel)  # No error bars for totals
            variant_positions[variant].append(x)
            variant_success[variant].append(-1)  # -1 indicates this is the total bar

    plt.figure(figsize=(max(10, len(kernels) * 0.6), 5))
    legend_handles = []
    for variant in labels:
        plt.bar(variant_positions[variant],
                variant_means[variant],
                yerr=variant_errs[variant],
                width=bar_width * 0.9,
                color=colors[variant],
                capsize=3,
                label=names[variant])
        legend_handles.append(Patch(facecolor=colors[variant], label=names[variant]))

    # Add success count on bottom of each bar
    for variant in labels:
        for pos, mean_val, err_val, success_count in zip(variant_positions[variant],
                                                          variant_means[variant],
                                                          variant_errs[variant],
                                                          variant_success[variant]):
            # Skip text for the total bar
            if success_count == -1:
                continue
            y_pos = 0 - 10
            text = "✗" if success_count == 0 else ("✓" if success_count == 10 else f"{success_count}")

            plt.text(pos, y_pos, text,
                    ha='center', va='bottom', fontsize=12, rotation=0)

    # Add absolute time labels beside Base bars only
    for i, (pos, mean_val, abs_time) in enumerate(zip(variant_positions['normal'], 
                                                        variant_means['normal'], 
                                                        base_absolutes)):
        if not np.isnan(mean_val):
            text_size = len(f'{int(round(abs_time))}s')
            thepos = pos-text_size*0.009-0.15 if level == 1 else pos-text_size*0.009-0.1
            y_pos = mean_val - text_size*5
            plt.text(thepos, y_pos, 
                    f'{int(round(abs_time))}s',
                    ha='center', va='bottom', fontsize=12, rotation=90)

    plt.axhline(100, color='gray', linestyle='--', linewidth=1)
    plt.xticks(kernel_positions, kernels, rotation=45, ha='right', position=(0,-0.03))
    plt.ylabel("Backend verification time (% of Base)")
    # plt.title(f"BLAS level {level} verification times (Base = 100%).")
    plt.legend(handles=legend_handles, title="Variant", loc="upper left", bbox_to_anchor=(1.02, 1))
    plt.tight_layout()
    out_path = f"{DIR}/results/blas_level{level}_barplot.pdf"
    plt.savefig(out_path)
    plt.close()

def generate_latex_main():
    latex = []
    latex.append("\\documentclass{article}")
    latex.append("\\usepackage{amssymb}")
    latex.append("\\usepackage{pifont}")
    latex.append("\\usepackage{booktabs}")
    latex.append("\\usepackage{subcaption}")
    latex.append("\\usepackage{colortbl}")
    latex.append("\\usepackage[dvipsnames]{xcolor}")
    latex.append("\\usepackage{graphicx}")
    latex.append("\\usepackage{siunitx}")
    latex.append("\\captionsetup[subfigure]{position=bottom}")
    latex.append("\\begin{document}")
    latex.append("\\newcommand{\\haliver}{HaliVer}")

    # latex.append("\\begin{table}[t]")
    # latex.append("\\centering")
    # latex.append("\\caption{\\label{tab:chp6-results-exp-mem}Verification results for the experiments of HaliVer from Chapter 4.}")
    # latex.append("\\input{" + DIR + "/results/exp-mem.tex}")
    # latex.append("\\end{table}")

    # latex.append("\\begin{table}[t]")
    # latex.append("\\centering")
    # latex.append("\\caption{\\label{tab:chp6-results-exp}Verification results for the experiments of HaliVer from Chapter 4.}")
    # latex.append("\\input{" + DIR + "/results/exp.tex}")
    # latex.append("\\end{table}")

    latex.append("\\begin{table}[t]")
    latex.append("\\centering")
    latex.append("\\input{" + DIR + "/results/blas_level1.tex}")
    latex.append("\\input{" + DIR + "/results/blas_level2.tex}")
    latex.append("""\\caption{\\label{tab:blas-results}Verification results for the clBLAS GPU kernels for level 1 and 2. 
\\textbf{Base} is the baseline configuration without any extra features. It is compared against versions with unique type qualifiers (\\textbf{Unique}), immutable arrays (\\textbf{Immutable}), extracted kernel bodies (\\textbf{Extract}), and a configuration enabling all features simultaneously (\\textbf{All}).
The $\\dagger$ indicates we (try to) prove functional correctness in addition to memory safety.
% A name marked with a $\\dagger$ indicates that \\textsc{VerCors} attempts to prove both memory safety and functional correctness of the kernel; otherwise, it only attempts to prove memory safety.
% $T_t$ denotes the average total verification time of VerCors, and $T_v$ the average time spent in the VerCors backend. Speedup$_v$ is the speedup of backend time relative to the baseline.
$\\#_{imm}$ and $\\#_p$ is the number of immutable and normal pointer arrays, respectively. $\\#_A$ the is the total number of annotations.}""")
    latex.append("\\end{table}")
    latex.append("\\begin{figure}[t]")
    latex.append("\\centering")
    
    latex.append("\\end{figure}")
    latex.append("\\begin{figure}[t]")
    latex.append("\\centering")
    latex.append("\\subfloat[\\label{fig:blas-barplot-level1}Level 1]{\\includegraphics[width=0.95\\textwidth]{" + DIR + "/results/blas_level1_barplot.pdf}}\\\\")
    latex.append("\\subfloat[\\label{fig:blas-barplot-level2}Level 2]{\\includegraphics[width=0.95\\textwidth]{" + DIR + "/results/blas_level2_barplot.pdf}}")
    latex.append("""\\caption{\\label{fig:blas-results}Verification backend times for the clBLAS GPU kernels for level 1 and 2, normalized so Base=100\\%. \\textbf{Base} is the baseline configuration without any extra features. It is compared against versions with unique type qualifiers (\\textbf{Unique}), immutable arrays (\\textbf{Immutable}), extracted kernel bodies (\\textbf{Extract}), and a configuration enabling all features simultaneously (\\textbf{All}). Bars show mean with standard error of the mean. Below the bars: \\checkmark = 10/10 successful, \\ding{55}  = 0/10 successful, else number of successful runs out of 10. Next to base bars: average time in seconds of the 10 base runs. The $\\dagger$ indicates we (try to) prove functional correctness in addition to memory safety.}""")
    latex.append("\\end{figure}")
    latex.append("\\end{document}")
    return "\n".join(latex)

def main(input_xml_blas_level1, input_xml_blas_level2, output_tex):
    # experiments, experiments_mem  = parse_xml_exp(input_xml_exp)
    # latex_exp = generate_latex_tabular_exp(experiments_mem, True)
    # with open(f"{DIR}/results/exp-mem.tex", 'w') as f:
    #     f.write("\n".join(latex_exp))

    # latex_exp = generate_latex_tabular_exp(experiments, False)
    # with open(f"{DIR}/results/exp.tex", 'w') as f:
    #     f.write("\n".join(latex_exp))

    for level in [1,2]:
        # if level == 1:
        #     continue
        experiments_padre = parse_xml(input_xml_blas_level1) if level == 1 else parse_xml(input_xml_blas_level2)
        latex_padre= generate_latex_blas(experiments_padre, level=level)
        with open(f"{DIR}/results/blas_level{level}.tex", 'w') as f:
            f.write(latex_padre)
        generate_blas_barplots(experiments_padre, level=level)
    # experiments_padre = parse_xml(input_xml_blas_level2)
    # latex_padre= generate_latex_padre(experiments_padre)
    # with open(f"{DIR}/results/blas_level2.tex", 'w') as f:
    #     f.write(latex_padre)

    latex_main = generate_latex_main()
    with open(output_tex, 'w') as f:
        f.write(latex_main)

    # Generate PDF using pdflatex
    subprocess.run(['pdflatex', '-output-directory', f'{DIR}/results', output_tex])
    out_base = output_tex.replace(".tex", "")
    subprocess.run(['rm', f"{out_base}.aux", f"{out_base}.log"])

if __name__ == "__main__":
    default_timestamp = "2025-12-14"
    parser = argparse.ArgumentParser(description='Run HaliVer experiments')
    parser.add_argument('--timestamp', 
                       default=default_timestamp, 
                       help=f"Timestamp for output files (default: {default_timestamp})")
    args = parser.parse_args()
    timestamp = args.timestamp
    
    # input_xml_exp = f"{DIR}/results/exp-{timestamp}.xml" 
    # input_xml_padre = f"{DIR}/results/padre-{timestamp}.xml"
    input_xml_blas_level1 = f"{DIR}/results/exp-level1-{timestamp}.xml"
    input_xml_blas_level2 = f"{DIR}/results/exp-level2-{timestamp}.xml"
    output_tex = f"{DIR}/results/table.tex"
    main(input_xml_blas_level1, input_xml_blas_level2, output_tex)