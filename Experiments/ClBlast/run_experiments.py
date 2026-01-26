import subprocess
import time
from lxml import etree as ET
from datetime import datetime
import os
import argparse
import re

DIR = os.path.dirname(os.path.abspath(__file__))
VCT = f"/home/lars/data/vercors/bin/vct"

def run_command(command):
    start_time = time.time()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    stdout, stderr = process.communicate()
    end_time = time.time()
    elapsed_time = end_time - start_time
    return process.returncode, elapsed_time, stdout.decode(), stderr.decode()

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
        print(f"Processing file ({tags}): {input_file}, i={i}")
        if (str(i), tags, input_file) in existing_results:
            result = existing_results[(str(i), tags, input_file)]
            print(f"  Skipping for i={i} and tags={tags}. Original result: {result['return_code']}")
        else:
            command = command_template.format(input_file=input_file, vct=VCT, timeout=timeout)
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

def experiments(output_xml, i, level=1, unique=False, const=False, extract=False,
                input_files=None, timeout=3600):
    if(input_files is None):
        # Read input files from a file
        with open(f'experiments{level}.txt', 'r') as file:
            input_files = [line.strip() for line in file.readlines()]
        input_files = [f"level{level}/{file}" for file in input_files]

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

    main(input_files, i, command_template, output_xml, tags, timeout=timeout)

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

    default_timestamp = "2025-12-14"
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
    input_files = None
    for i in range(repetitions):
      for l in [1, 2]:
        file = f"results/exp-level{l}-{timestamp}.xml"
        experiments(file, i, level=l, unique=True, const=True, extract=True, input_files=input_files,timeout=timeout)
        experiments(file, i, level=l, unique=True, input_files=input_files,timeout=timeout)
        experiments(file, i, level=l, const=True, input_files=input_files,timeout=timeout)
        experiments(file, i, level=l, extract=True, input_files=input_files,timeout=timeout)
        experiments(file, i, level=l, input_files=input_files,timeout=timeout)
    