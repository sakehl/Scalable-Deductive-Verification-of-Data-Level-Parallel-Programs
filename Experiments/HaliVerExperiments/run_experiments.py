import subprocess
import time
from lxml import etree as ET
from datetime import datetime
import os
import argparse
import re
import shutil

DIR = os.path.dirname(os.path.abspath(__file__))
VCT = shutil.which("vct")
BUILD = os.path.join(DIR, "build")

def run_command(command):
    start_time = time.time()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    stdout, stderr = process.communicate()
    end_time = time.time()
    elapsed_time = end_time - start_time
    return process.returncode, elapsed_time, stdout.decode(), stderr.decode()

def create_xml_element(tag, text):
    element = ET.Element(tag)
    element.text = text
    return element

def prettify_xml(element):
    rough_string = ET.tostring(element, pretty_print=True, encoding='UTF-8').decode('UTF-8')
    # Add XSLT reference
    xslt_ref = '<?xml-stylesheet type="text/xsl" href="style.xsl"?>\n'
    return xslt_ref + rough_string

def parse_existing_results(output_xml):
    existing_results = {}
    if os.path.exists(output_xml):
        try:
            tree = ET.parse(output_xml)
            root = tree.getroot()
            for group in root.findall('group'):
                i = group.find('i').text
                tags_elem = group.find('tags')
                tags = tags_elem.text if tags_elem is not None else "normal"
                for file in group.findall('file'):
                    input_file = file.find('name').text
                    result = {
                        'return_code': file.find('return_code').text,
                        'elapsed_time': file.find('elapsed_time').text,
                        'stdout': file.find('stdout').text,
                        'stderr': file.find('stderr').text
                    }
                    existing_results[(i, tags, input_file)] = result
        except Exception as e:
            print(f"Error parsing existing results: {e}")
    return existing_results

def format_remaining_time(seconds):
    if seconds is None:
        return "?"

    total_minutes = int((seconds + 59) // 60)
    if total_minutes <= 0:
        return "0m"
    if total_minutes > 60:
        total_hours = int((total_minutes + 59) // 60)
        remaining_minutes = int((total_minutes + 59) % 60)
        return f"{total_hours:2d}h{remaining_minutes:02d}m"
    return f"   {total_minutes:02d}m"

def estimate_remaining_seconds_from_i0(i0_times, current_index):
    if not i0_times or current_index < 0:
        return None
    return sum(i0_times[current_index:])

def extract_backend_duration(stdout):
    match = re.search(r"Done: BackendVerification \(at [^,]+, duration: (\d+):(\d+):(\d+)\)", stdout)
    if match:
        hours, minutes, seconds = map(int, match.groups())
        return hours * 3600 + minutes * 60 + seconds
    return None

def extract_total_duration(stdout):
    match = re.search(r"Done: VerCors \(at [^,]+, duration: (\d+):(\d+):(\d+)\)", stdout)
    if match:
        hours, minutes, seconds = map(int, match.groups())
        return hours * 3600 + minutes * 60 + seconds
    return None

def build_experiment_input_files(non_unique=False, mem=False):
    with open('experiments.txt', 'r') as file:
        names = [line.strip() for line in file.readlines()]

    postfix = ("_mem" if mem else "")
    postfix = postfix + ("_non_unique" if non_unique else "")
    input_files = [f"{file}_{v}{postfix}.c" for file in names for v in range(0, 4)]

    if mem:
        with open('experiments_mem.txt', 'r') as file:
            mem_names = [line.strip() for line in file.readlines()]
        input_files = input_files + [f"{file}{postfix}.c" for file in mem_names]

    tags = "normal" if postfix == "" else postfix
    return input_files, tags

def build_padre_input_files(non_unique=False, cb=False):
    names = ["StepHalide", "SubDirectionHalide", "SolveDirectionHalide", "PerformIterationHalide"]
    postfix = ("CB" if cb else "")
    postfix = postfix + ("_non_unique" if non_unique else "")

    input_files = [f"{file}{postfix}.c" for file in names]
    tags = "normal" if postfix == "" else postfix
    return input_files, tags

def collect_i0_durations(plan_entries, timeout):
    i0_times = []
    results_by_file = {}

    for output_xml, tags, input_file in plan_entries:
        if output_xml not in results_by_file:
            results_by_file[output_xml] = parse_existing_results(output_xml)
        existing_results = results_by_file[output_xml]

        key = ('0', tags, input_file)
        if key not in existing_results:
            continue
        try:
            elapsed = float(existing_results[key]['elapsed_time'])
        except (TypeError, ValueError):
            continue
        i0_times.append(min(elapsed, float(timeout)))

    return i0_times

def main(input_files, i, command_template, output_xml, tags, timeout, i0_times):
    existing_results = parse_existing_results(output_xml)
    global current
    global total
    
    # Read existing results.xml if it exists
    if os.path.exists(output_xml):
        # try:
        tree = ET.parse(output_xml)
        root = tree.getroot()
        # except:
        #     root = ET.Element("results")
    else:
        root = ET.Element("results")
    
    # Check if the group already exists
    group_element = None
    for group in root.findall('group'):
        if group.find('i').text == str(i) and group.find('tags').text == tags:
            group_element = group
            break
    
    result_dict = {
        '0': "✓",
        '1': "✗",
        '2': "-",
        '3': "T.O."
    }

    # Add a new group for the current run if it does not exist
    if group_element is None:
        group_element = ET.Element("group")
        group_element.append(create_xml_element("i", f"{i}"))
        group_element.append(create_xml_element("tags", tags))
        root.append(group_element)
        
    for input_file in input_files:
        remaining_seconds = estimate_remaining_seconds_from_i0(i0_times, current - 1)
        remaining_label = format_remaining_time(remaining_seconds)
        name = f"'{input_file}'"
        print(f"[{current:3}/{total}, {remaining_label}] Verifying {name:>43}... ", end="", flush=True)
        current += 1

        key = (str(i), tags, input_file)
        if key in existing_results:
            result = existing_results[key]
            backend_time = extract_backend_duration(result['stdout'])
            backend_time = str(backend_time) + 's' if backend_time is not None else ''
            total_time = extract_total_duration(result['stdout'])
            total_time = str(total_time) + 's' if total_time is not None else ''
            rc = result['return_code']
            print(f"{result_dict.get(rc, rc):>4} {total_time:>5} (backend: {backend_time:>5}) (stored result)")
        else:
            command = command_template.format(input_file=input_file, vct=VCT, build=BUILD, timeout=timeout)
            return_code, elapsed_time, stdout, stderr = run_command(command)
            file_element = ET.Element("file")
            file_element.append(create_xml_element("name", input_file))
            file_element.append(create_xml_element("return_code", str(return_code)))
            file_element.append(create_xml_element("elapsed_time", str(elapsed_time)))
            file_element.append(create_xml_element("stdout", stdout))
            file_element.append(create_xml_element("stderr", stderr))
            backend_time = extract_backend_duration(stdout)
            backend_time = str(backend_time) + 's' if backend_time is not None else ''
            total_time = extract_total_duration(stdout)
            total_time = str(total_time) + 's' if total_time is not None else ''
            if not return_code in [0,1,2,3]:
                print("Error occured")
                print(stdout)
                print(stderr)
                exit()
            print(f"{result_dict.get(str(return_code), str(return_code)):>4} {total_time:>5} (backend: {backend_time:>5})")
            group_element.append(file_element)
        
        # Update the XML file after each file is processed
        with open(output_xml, "w") as xml_file:
            xml_file.write(prettify_xml(root))
    
    # Update the XML file after processing all files
    with open(output_xml, "w") as xml_file:
        xml_file.write(prettify_xml(root))

def experiments(output_xml, i, non_unique=False, mem=False, timeout=3600, i0_times=None):
    input_files, tags = build_experiment_input_files(non_unique=non_unique, mem=mem)

    command_template = "{vct} --no-infer-heap-context-into-frame --silicon-quiet --dev-time-backend --dev-total-timeout={timeout} --dev-assert-timeout 60 --target x86_64-linux-gnu {build}/{input_file}"
    if i0_times is None:
        i0_times = []
    main(input_files, i, command_template, output_xml, tags, timeout, i0_times)

def padre(output_xml, i, non_unique=False, cb=False, timeout=3600, i0_times=None):
    input_files, tags = build_padre_input_files(non_unique=non_unique, cb=cb)
    command_template = "{vct} --no-infer-heap-context-into-frame --silicon-quiet --dev-time-backend --dev-total-timeout={timeout} --dev-assert-timeout 60 --target x86_64-linux-gnu {build}/{input_file}"
    if i0_times is None:
        i0_times = []
    main(input_files, i, command_template, output_xml, tags, timeout, i0_times)

def remove_entry(output_xml, i, tags, input_file, only_if_error=False):
    """Remove a specific entry from the results XML file."""
    if not os.path.exists(output_xml):
        print(f"File {output_xml} does not exist.")
        return False
    
    try:
        tree = ET.parse(output_xml)
        root = tree.getroot()
        
        for group in root.findall('group'):
            if group.find('i').text == str(i) and group.find('tags').text == tags:
                for file_elem in group.findall('file'):
                    if file_elem.find('name').text == input_file:
                        if only_if_error:
                            return_code = file_elem.find('return_code').text
                            if return_code != '2':
                                print(f"Entry has no error, not removing: i={i}, tags={tags}, file={input_file}")
                                return False
                        
                        group.remove(file_elem)
                        print(f"Removed entry: i={i}, tags={tags}, file={input_file}")
                        
                        # If group is now empty, remove the group
                        if len(group.findall('file')) == 0:
                            root.remove(group)
                            print(f"Removed empty group: i={i}, tags={tags}")
                        
                        with open(output_xml, "w") as xml_file:
                            xml_file.write(prettify_xml(root))
                        return True
        
        print(f"Entry not found: i={i}, tags={tags}, file={input_file}")
        return False
    except Exception as e:
        print(f"Error removing entry: {e}")
        return False

if __name__ == "__main__":
    default = "2026-01-12"
    parser = argparse.ArgumentParser(description='Run HaliVer experiments')
    parser.add_argument('--timestamp', 
                       default=default, 
                       help=f'Timestamp for output files (default: {default})')

    parser.add_argument('--repetitions', 
                       default=1, 
                       type=int,
                       help='Number of repetitions for each experiment (default: 1)')

    parser.add_argument('--timeout', 
                       default=3600, 
                       type=int,
                       help='Timeout for each experiment (default: 3600)')
    
    parser.add_argument('--remove',
                    nargs=4,
                    metavar=('OUTPUT_XML', 'I', 'TAGS', 'INPUT_FILE'),
                    help='Remove a specific entry from results: output_xml i tags input_file')

    args = parser.parse_args()

    # Handle remove operation
    if args.remove:
        output_xml, i, tags, input_file = args.remove
        remove_entry(output_xml, i, tags, input_file)
        exit(0)

    timestamp = args.timestamp
    repetitions = args.repetitions
    timeout = args.timeout
    assert repetitions > 0
    assert timeout > 0

    exp_file = os.path.join("results", f"exp-{timestamp}.xml")
    padre_file = os.path.join("results", f"padre-{timestamp}.xml")

    run_configs = [
        ("experiments", {"non_unique": False, "mem": False}, exp_file),
        ("experiments", {"non_unique": True, "mem": False}, exp_file),
        ("experiments", {"non_unique": False, "mem": True}, exp_file),
        ("experiments", {"non_unique": True, "mem": True}, exp_file),
        ("padre", {"non_unique": False, "cb": False}, padre_file),
        ("padre", {"non_unique": True, "cb": False}, padre_file),
        ("padre", {"non_unique": False, "cb": True}, padre_file),
        ("padre", {"non_unique": True, "cb": True}, padre_file),
    ]

    one_rep_plan = []
    for kind, flags, output_xml in run_configs:
        if kind == "experiments":
            files, tags = build_experiment_input_files(non_unique=flags["non_unique"], mem=flags["mem"])
        else:
            files, tags = build_padre_input_files(non_unique=flags["non_unique"], cb=flags["cb"])
        one_rep_plan.extend((output_xml, tags, input_file) for input_file in files)

    global total
    total = len(one_rep_plan) * repetitions
    global current
    current = 1

    i0_times = collect_i0_durations(one_rep_plan, timeout)
    i0_times = i0_times * repetitions

    print(f"Total experiments to run is {total}. Estimated time: {format_remaining_time(sum(i0_times) if i0_times else None)}")

    for i in range(repetitions):
        experiments(exp_file, i, timeout=timeout, i0_times=i0_times)
        experiments(exp_file, i, non_unique=True, timeout=timeout, i0_times=i0_times)
        experiments(exp_file, i, mem=True, timeout=timeout, i0_times=i0_times)
        experiments(exp_file, i, non_unique=True, mem=True, timeout=timeout, i0_times=i0_times)

        padre(padre_file, i, timeout=timeout, i0_times=i0_times)
        padre(padre_file, i, non_unique=True, timeout=timeout, i0_times=i0_times)
        padre(padre_file, i, cb=True, timeout=timeout, i0_times=i0_times)
        padre(padre_file, i, cb=True, non_unique=True, timeout=timeout, i0_times=i0_times)