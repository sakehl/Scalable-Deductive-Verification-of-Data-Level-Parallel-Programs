import subprocess
import time
from lxml import etree as ET
from datetime import datetime
import os
import argparse
import re
import shutil
import shlex

DIR = os.path.dirname(os.path.abspath(__file__))
VCT = shutil.which("vct") or "vct"

def run_command(command):
    start_time = time.time()
    # Avoid shell-specific behavior differences; run as argv for stable stdout/stderr capture.
    if isinstance(command, str):
        command = shlex.split(command)
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()
    end_time = time.time()
    elapsed_time = end_time - start_time
    return process.returncode, elapsed_time, stdout.decode(errors='replace'), stderr.decode(errors='replace')

def sanitize_text(text: str) -> str:
  if text is None:
    return ""
  # Remove disallowed XML control chars (except tab, newline, carriage return)
  text = re.sub(r'[\x00-\x08\x0B\x0C\x0E-\x1F]', '', text)
  # Optionally trim extremely long outputs to avoid huge XML files
  return text

def create_xml_element(tag, text):
    element = ET.Element(tag)
    element.text = sanitize_text(text)
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
                tags = group.find('tags').text
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

def collect_i0_durations(output_xml_files, input_files, timeout):
    i0_times = []
    tags = ["unique-const-extract", "unique", "const", "extract", "normal"]
    total_time = 0.0
    for l in [1, 2]:
        existing_results = parse_existing_results(output_xml_files[l])
        for t in tags:
            for input_file in input_files[l]:
                averages = []
                for i in range(10):
                    if (str(i), t, input_file) in existing_results:
                        result = existing_results[(str(i), t, input_file)]
                        backend_time = extract_backend_duration(result['stdout'])
                        time = extract_total_duration(result['stdout'])
                        parse_time = time - backend_time
                        time = parse_time + min(backend_time, float(timeout))
                        averages.append(time)
                if averages:
                    avg_time = sum(averages) / len(averages)
                    i0_times.append(avg_time)
                    total_time += avg_time
    return i0_times

def estimate_remaining_seconds_from_i0(i0_times, current):
    if not i0_times or current < 0:
        return None

    return sum(i0_times[current:])
    

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
    
def extract_backend_duration(stdout):
    if stdout is None:
        return None
    match = re.search(r"Done: BackendVerification \(at [^,]+, duration: (\d+):(\d+):(\d+)\)", stdout)
    if match:
        hours, minutes, seconds = map(int, match.groups())
        return hours * 3600 + minutes * 60 + seconds
    return None

def extract_total_duration(stdout):
    if stdout is None:
        return None
    match = re.search(r"Done: VerCors \(at [^,]+, duration: (\d+):(\d+):(\d+)\)", stdout)
    if match:
        hours, minutes, seconds = map(int, match.groups())
        return hours * 3600 + minutes * 60 + seconds
    return None

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
        remaining_seconds = estimate_remaining_seconds_from_i0(i0_times, current-1)
        remaining_label = format_remaining_time(remaining_seconds)
        name = f"'{input_file}'"
        print(f"[{current:3}/{total}, {remaining_label}] Verifying {name:17} ... ", end="", flush=True)
        current += 1
        if (str(i), tags, input_file) in existing_results:
            result = existing_results[(str(i), tags, input_file)]
            backend_time = extract_backend_duration(result['stdout'])
            backend_time = str(backend_time) + 's' if backend_time is not None else ''
            time = extract_total_duration(result['stdout'])
            time = str(time) + 's' if time is not None else ''
            print(f"{result_dict[result['return_code']]:>4} {time:>5} (backend: {backend_time:>5}) (stored result)")
        else:
            command = command_template.format(input_file=input_file, vct=VCT, timeout=timeout)
            return_code, elapsed_time, stdout, stderr = run_command(command)
            combined_output = f"{stdout}\n{stderr}" if stderr else stdout
            file_element = ET.Element("file")
            file_element.append(create_xml_element("name", input_file))
            file_element.append(create_xml_element("return_code", str(return_code)))
            file_element.append(create_xml_element("elapsed_time", str(elapsed_time)))
            file_element.append(create_xml_element("stdout", stdout))
            file_element.append(create_xml_element("stderr", stderr))
            backend_time = extract_backend_duration(combined_output)
            backend_time = str(backend_time) + 's' if backend_time is not None else ''
            time = extract_total_duration(combined_output)
            time = str(time) + 's' if time is not None else ''
            if not return_code in [0,1,2,3]:
                print("Error occured")
                print(stdout)
                print(stderr)
                exit()
            print(f"{result_dict[str(return_code)]:>4} {time:>5} (backend: {backend_time:>5})")
            group_element.append(file_element)
        
        # Update the XML file after each file is processed
        with open(output_xml, "w") as xml_file:
            xml_file.write(prettify_xml(root))
    
    # Update the XML file after processing all files
    with open(output_xml, "w") as xml_file:
        xml_file.write(prettify_xml(root))

def experiments(output_xml, i, input_files, unique=False, const=False, extract=False,
                timeout=3600, i0_times=None):

    command_template = f"{{vct}} --silicon-quiet --dev-time-backend --dev-total-timeout={timeout} --dev-assert-timeout 60 --target x86_64-linux-gnu {{input_file}}"
    first = False
    if unique or const or extract:
        command_template += " --c-define "
    if unique:
        command_template += "UNIQUE_TYPES=1"
        first = True
    if const:
        if first:
            command_template += ","
        command_template += "CONST_TYPES=1"
        first = True
    if extract:
        if first:
            command_template += ","
        command_template += "EXTRACT_BODY=1"
        first = True
    if unique and const and extract:
        tags = "unique-const-extract"
    elif unique:
        tags = "unique"
    elif const:
        tags = "const"
    elif extract:
        tags = "extract"
    else:
        tags = "normal"

    if i0_times is None:
        i0_times = []
    main(input_files, i, command_template, output_xml, tags, timeout=timeout, i0_times=i0_times)

def clean_errors(output_xml):
    existing_results = parse_existing_results(output_xml)
    for (i, tags, input_file), result in existing_results.items():
        if result['return_code'] == '2':
            remove_entry(output_xml, i, tags, input_file, only_if_error=True)

def clean_timeouts(output_xml):
    existing_results = parse_existing_results(output_xml)
    for (i, tags, input_file), result in existing_results.items():
        if result['return_code'] == '3':
            remove_entry(output_xml, i, tags, input_file, only_if_error=False)

if __name__ == "__main__":

    default_timestamp = "2026-04-23"
    # default_timestamp = "2025-12-14"
    parser = argparse.ArgumentParser(description='Run experiments for CLBlast with Vercors verification.')
    parser.add_argument('--timestamp', 
                       default=default_timestamp, 
                       help=f'Timestamp for output files (default: {default_timestamp})')

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
    
    parser.add_argument('--clean-errors',
                       nargs=1,
                       metavar=('OUTPUT_XML'),
                       help='Remove all error entries from results: output_xml')

    args = parser.parse_args()
    
    # Handle remove operation
    if args.remove:
        output_xml, i, tags, input_file = args.remove
        remove_entry(output_xml, i, tags, input_file)
        exit(0)

    # Handle clean errors operation
    if args.clean_errors:
        output_xml = args.clean_errors[0]
        clean_errors(output_xml)
        exit(0)

    timestamp = args.timestamp
    repetitions = args.repetitions
    timeout = args.timeout
    assert repetitions > 0
    assert timeout > 0

    # input_files = ["level2/xger.cl", "level2/xher.cl", "level2/xher2.cl", "level2/xtrsv.cl"]
    input_files = {}
    global total
    total = 0
    
    # Read input files from a file
    for l in [1, 2]:
        with open(f'experiments{l}.txt', 'r') as file:
            input_files[l] = [line.strip() for line in file.readlines()]
            input_files[l] = [os.path.join(f"level{l}", file) for file in input_files[l]]
            total += len(input_files[l])
    total = 5 * total * repetitions
    global current
    current = 1

    old_result_files = {l : os.path.join("results", f"exp-level{l}-2025-12-14.xml") 
                        for l in [1, 2]}
    result_files = {l : os.path.join("results", f"exp-level{l}-{timestamp}.xml")
                        for l in [1, 2]}
    i0_times = collect_i0_durations(old_result_files, input_files, timeout)
    i0_times = i0_times * repetitions
    
    print(f"Total experiments to run is {total}. Estimated time: {format_remaining_time(sum(i0_times))}")
    for i in range(repetitions):
      for l in [1, 2]:
        file = result_files[l]
        print(f"Running experiments for level {l} (i={i}, tags=unique-immutable-extract)...")
        experiments(file, i, input_files[l], unique=True, const=True, extract=True, timeout=timeout, i0_times=i0_times)
        print(f"Running experiments for level {l} (i={i}, tags=unique)...")
        experiments(file, i, input_files[l], unique=True, timeout=timeout, i0_times=i0_times)
        print(f"Running experiments for level {l} (i={i}, tags=immutable)...")
        experiments(file, i, input_files[l], const=True, timeout=timeout, i0_times=i0_times)
        print(f"Running experiments for level {l} (i={i}, tags=extract)...")
        experiments(file, i, input_files[l], extract=True, timeout=timeout, i0_times=i0_times)
        print(f"Running experiments for level {l} (i={i}, tags=normal)...")
        experiments(file, i, input_files[l], timeout=timeout, i0_times=i0_times)
    