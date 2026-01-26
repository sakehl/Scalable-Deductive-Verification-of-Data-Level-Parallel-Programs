import subprocess
import time
from lxml import etree as ET
from datetime import datetime
import os
import argparse

DIR = os.path.dirname(os.path.abspath(__file__))
VCT = f"../../../vercors/bin/vct"
BUILD = f"{DIR}/build"

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
                for file in group.findall('file'):
                    input_file = file.find('name').text
                    result = {
                        'return_code': file.find('return_code').text,
                        'elapsed_time': file.find('elapsed_time').text,
                        'stdout': file.find('stdout').text,
                        'stderr': file.find('stderr').text
                    }
                    existing_results[(i, input_file)] = result
        except Exception as e:
            print(f"Error parsing existing results: {e}")
    return existing_results

def main(input_files, i, command_template, output_xml, tags, timeout):
    existing_results = parse_existing_results(output_xml)
    
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
    
    # Add a new group for the current run if it does not exist
    if group_element is None:
        group_element = ET.Element("group")
        group_element.append(create_xml_element("i", f"{i}"))
        group_element.append(create_xml_element("tags", tags))
        root.append(group_element)
    
    for input_file in input_files:
        print(f"Processing file: {input_file}, i={i}")
        if (str(i), input_file) in existing_results:
            result = existing_results[(str(i), input_file)]
            print(f"  Skipping for i={i}. Original result: {result['return_code']}")
        else:
            command = command_template.format(input_file=input_file, vct=VCT, build=BUILD, timeout=timeout)
            return_code, elapsed_time, stdout, stderr = run_command(command)
            file_element = ET.Element("file")
            file_element.append(create_xml_element("name", input_file))
            file_element.append(create_xml_element("return_code", str(return_code)))
            file_element.append(create_xml_element("elapsed_time", str(elapsed_time)))
            file_element.append(create_xml_element("stdout", stdout))
            file_element.append(create_xml_element("stderr", stderr))
            print(f"  Return code was: {return_code}")
            group_element.append(file_element)
        
        # Update the XML file after each file is processed
        with open(output_xml, "w") as xml_file:
            xml_file.write(prettify_xml(root))
    
    # Update the XML file after processing all files
    with open(output_xml, "w") as xml_file:
        xml_file.write(prettify_xml(root))

def experiments(output_xml, i, non_unique=False, mem=False, timeout=3600):
    # Read input files from a file
    with open('experiments.txt', 'r') as file:
        names = [line.strip() for line in file.readlines()]
    
    postfix = ("_mem" if mem else "")
    postfix = postfix + ("_non_unique" if non_unique else "")

    input_files = [f"{file}_{v}{postfix}.c" for file in names for v in range(0,4)]

    if(mem):
        with open('experiments_mem.txt', 'r') as file:
            mem_names = [line.strip() for line in file.readlines()]
        input_files = input_files + [f"{file}{postfix}.c" for file in mem_names]
 
    command_template = "{vct} --no-infer-heap-context-into-frame --silicon-quiet --dev-time-backend --dev-total-timeout={timeout} --dev-assert-timeout 60 --target x86_64-linux-gnu {build}/{input_file}"
    tags = "normal" if postfix == "" else postfix
    main(input_files, i, command_template, output_xml, tags, timeout)

def padre(output_xml, i, non_unique=False, cb=False, timeout=3600):
    names = ["StepHalide", "SubDirectionHalide", "SolveDirectionHalide", "PerformIterationHalide"]
    postfix = ("CB" if cb else "")
    postfix = postfix + ("_non_unique" if non_unique else "")

    input_files = [f"{file}{postfix}.c" for file in names]
    command_template = "{vct} --no-infer-heap-context-into-frame --silicon-quiet --dev-time-backend --dev-total-timeout={timeout} --dev-assert-timeout 60 --target x86_64-linux-gnu {build}/{input_file}"
    tags = "normal" if postfix == "" else postfix
    main(input_files, i, command_template, output_xml, tags, timeout)

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

    for i in range(repetitions):
        file = f"results/exp-{timestamp}.xml"
        experiments(file, i, timeout=timeout)
        experiments(file, i, non_unique=True, timeout=timeout)

        experiments(file, i, mem=True, timeout=timeout)
        experiments(file, i, non_unique=True, mem=True, timeout=timeout)
        file = f"results/padre-{timestamp}.xml"
        padre(file, i, timeout=timeout)
        padre(file, i, non_unique=True, timeout=timeout)
        padre(file, i, cb=True, timeout=timeout)
        padre(file, i, cb=True, non_unique=True, timeout=timeout)