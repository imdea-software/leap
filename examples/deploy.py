#!/usr/bin/python

import sys
import platform
import argparse
import shutil
from os.path import join, isfile, isdir, split, exists, abspath, dirname
from os import system, devnull, listdir, mkdir, remove, environ
from subprocess import call, Popen, PIPE
from collections import namedtuple


# Configuration
machine = platform.node() + '_' + platform.system()
trunk_folder = '..'
deployment_folder = 'deployment'
testing_folder = 'testing'
result_folder = 'test_results'
summary_file = 'test_summary'
all_examples = 'all_examples'
history_file = machine + '.history'


# Type declaration
Case = namedtuple("Case", 'name content')


# Result keys
keys = ['R_NAME', 'R_TOTAL_VC', 'R_TOTAL_OBLIG', 'R_FASTEST', 'R_SLOWEST', 'R_AVERAGE',
        'R_TOTAL_DP', 'R_UNVERIFIED_VC', 'R_VALID_VC', 'R_INVALID_VC', 'R_DP_VC',
        'R_DP_CALLS', 'R_LEAP_TIME', 'R_TOTAL_ANALYSIS']


def key_to_str(key):
  if key == 'R_NAME'            : return ('"Name"')
  if key == 'R_TOTAL_VC'        : return ('"Total number of VC"')
  if key == 'R_TOTAL_OBLIG'     : return ('"Total number of proof obligations"')
  if key == 'R_FASTEST'         : return ('"Fastest time for verifying a single VC"')
  if key == 'R_SLOWEST'         : return ('"Slowest time for verifying a single VC"')
  if key == 'R_AVERAGE'         : return ('"Average time for verifying a single VC"')
  if key == 'R_TOTAL_DP'        : return ('"Total time for verifying all VCs"')
  if key == 'R_UNVERIFIED_VC'   : return ('"Total number of unverified VCs"')
  if key == 'R_VALID_VC'        : return ('"Total number of valid VCs"')
  if key == 'R_INVALID_VC'      : return ('"Total number of invalid VCs"')
  if key == 'R_DP_VC'           : return ('"Total number of VCs verified with each DP"')
  if key == 'R_DP_CALLS'        : return ('"Total number of calls performed to each DP"')
  if key == 'R_LEAP_TIME'       : return ('"Total analysis time employed by Leap without DP"')
  if key == 'R_TOTAL_ANALYSIS'  : return ('"Total analisys time including Leap reasoning and DP"')



# Initialization
current_path = sys.path[0]
trunk_path = join(current_path, trunk_folder)
deployment_path = join(current_path, deployment_folder)
testing_path = join(current_path, testing_folder)
results_path = join(current_path, testing_folder, result_folder)
summary_path = join(results_path, summary_file)
history_path = join(current_path, history_file)
leap_path = abspath(join(trunk_path, 'bin'))
cmd_compile_leap = ['make', 'leap']
FNULL = open(devnull, 'w')


# Auxiliary functions
def print_info(str):
  sys.stdout.write(str)
  sys.stdout.flush()


def test_call(status):
  if status == 0:
    print '[OK]'
  else:
    print '[X]'
    sys.exit(1)


def list_files_of_type(path,ext):
  return [f for f in listdir(path) if isfile(join(path,f)) and f.lower().endswith(ext)]


def list_folders(path):
  return [d for d in listdir(path) if isdir(join(path,d))]


def delete_folder(folder):
  shutil.rmtree(folder, ignore_errors=True)


def create_folder(folder):
  delete_folder(folder)
  mkdir (folder)


def error(msg):
  print 'ERROR: ' + msg
  sys.exit(1)


def print_separator():
  print ('=' * 80)


def print_med_separator():
  print ('-' * 80)


def print_short_separator():
  print ('-' * 60)


def error(msg):
  print ('[ ERROR   ] ***  {}  ***'.format(msg))


def change(msg):
  print ('[ CHANGE  ] ***  {}  ***'.format(msg))


def warning(msg):
  print ('[ WARNING ] ***  {}  ***'.format(msg))


def head_msg(msg):
  print ('\n===[  ' + msg + '  ]' + ('=' * (71 - len(msg))))


def middle_msg(msg):
  print ('\n---[  ' + msg + '  ]' + ('-' * (71 - len(msg))))


def short_msg(msg):
  print ('--  ' + msg + '  ' + ('-' * (54 - len(msg))))


# Path environment variable
def update_env_path():
  old_path = environ['PATH']
  leap_loc = Popen(['which', 'leap'], stdout=PIPE).communicate()[0]
  if leap_loc.strip() <> '':
    new_path = [p for p in old_path.split(':') if dirname(leap_loc) not in p]
  else:
    new_path = [p for p in old_path.split(':')]
  new_path.append(leap_path)
  environ['PATH'] = ':'.join(new_path)
  return old_path


# Zip files
def zip(path, files, zip_file):
  zip_proc = Popen(['zip', '-r', '-9', zip_file+'.zip', files], cwd=path, stdout=FNULL)
  if zip_proc.wait() <> 0:
    error ('Could not zip ' + files)


def unzip(path, zip_file):
  unzip_proc = Popen(['unzip', zip_file], cwd=path, stdout=FNULL)
  if unzip_proc.wait() <> 0:
    error ('Could not unzip ' + zip_file)


# Clean examples
def clean_examples(examples):
  print 'Cleaning examples...'
  delete_folder(deployment_path)
  delete_folder(testing_path)
  for k in examples.keys():
    for ex in examples[k]:
      folder = join(current_path, k, ex)
      system ('for i in `find ' + folder + ' -type f | grep \.vcfile` ; do rm -f $i ; done')
      system ('for i in `find ' + folder + ' -type f | grep \.sw` ; do rm -f $i ; done')


# Graph parsing
def parse_graph_cases(graph_lines):
  case = ''
  buf = ''
  found = []
  for line in graph_lines:
    normline = line.strip()
    if normline.startswith('->') or normline.startswith('=>'):
      if buf.strip() <> '':
        found.append(Case(name=case, content=buf))
        buf = ''
      case = line.split('>')[1].split('[')[0].split('{')[0].strip()
    buf = buf + line
  found.append(Case(name=case, content=buf))
  return found


# Script execution and results parsing
def parse_result_line(line,rs,key,expr):
  if expr in line:
    rs.append((key, line.split(':')[1].strip()))


def parse_dps(line):
  return [(dp.split(':')[0].strip(), dp.split(':')[1].strip()) for dp in line.split(';')]


def run_script(script,k,ex,case_name):
  summary_started = False
  dp_vc = False
  dp_calls = False
  results = [('R_NAME', '{}_{}_{}'.format(k,ex,case_name))]

  out_file = join(results_path, (ex + '_' + case_name + '.output'))
  (folder,sh) = split(script)
  out = open (out_file, 'w')
  out.seek(0)
  out.truncate()
  run = Popen('./' + sh, cwd=folder, stdout=PIPE, stderr=FNULL)
  for line in run.stdout:
    out.write (line)
    summary_started = summary_started or 'Summary' in line
    if summary_started:
      if dp_vc:
        results.append(('R_DP_VC',parse_dps(line)))
      if dp_calls:
        results.append(('R_DP_CALLS',parse_dps(line)))
      dp_vc = False
      dp_calls = False
      parse_result_line (line, results, 'R_TOTAL_OBLIG', 'Total proof obligations')
      parse_result_line (line, results, 'R_TOTAL_ANALYSIS', 'Total Analysis time')
      parse_result_line (line, results, 'R_FASTEST', 'Fastest')
      parse_result_line (line, results, 'R_SLOWEST', 'Slowest')
      parse_result_line (line, results, 'R_AVERAGE', 'Average')
      parse_result_line (line, results, 'R_TOTAL_DP', 'Total DP')
      parse_result_line (line, results, 'R_TOTAL_VC', 'Total VC')
      parse_result_line (line, results, 'R_UNVERIFIED_VC', 'Unverified')
      parse_result_line (line, results, 'R_VALID_VC', 'Valid')
      parse_result_line (line, results, 'R_INVALID_VC', 'Invalid')
      if 'Decision procedures for each VC' in line:
        dp_vc = True
      if 'Decision procedures total calls' in line:
        dp_calls = True
  
  if run.wait() == 0:
    print '[ OK ]'
  else:
    print '[ XX ]'
  # Values obtained from previously computed results
  results.append(('R_LEAP_TIME', float(dict(results)['R_TOTAL_ANALYSIS']) -
                                 float(dict(results)['R_TOTAL_DP'])))
  out.close()
  return results


# Summary output
def write_summary_head(out):
  out.write ('{:<30}{:>8}{:>8}{:>8}{:>8}{:>8}{:>11}{:>11}{:>11}{:>11}{:>11}{:>11} {:<40}{}\n'.format(
              'Example', 'VCS', 'Oblig', 'Unverif', 'Valid', 'Invalid', 'Fastest',
              'Slowest', 'Average', 'Total DP', 'Leap', 'Total', 'VC calls', 'Oblig. calls'))
  out.write ('=' * 218 + '\n')
  out.flush()


def write_summary_line(out,results):
  results_dict = dict(results)
  out.write ('{:<30}{:>8}{:>8}{:>8}{:>8}{:>8}{:11.2f}{:11.2f}{:11.2f}{:11.2f}{:11.2f}{:11.2f}  {:<40}{}\n'.format(
        results_dict['R_NAME'],
        results_dict['R_TOTAL_VC'],
        results_dict['R_TOTAL_OBLIG'],
        results_dict['R_UNVERIFIED_VC'],
        results_dict['R_VALID_VC'],
        results_dict['R_INVALID_VC'],
        float(results_dict['R_FASTEST']),
        float(results_dict['R_SLOWEST']),
        float(results_dict['R_AVERAGE']),
        float(results_dict['R_TOTAL_DP']),
        float(results_dict['R_LEAP_TIME']),
        float(results_dict['R_TOTAL_ANALYSIS']),
        '--'.join([dp + ':' + n for (dp,n) in results_dict['R_DP_VC']]),
        '--'.join([dp + ':' + n for (dp,n) in results_dict['R_DP_CALLS']])))
  out.flush()


# Sumamry input
def read_summary_file(filename):
  info = []
  in_file = open(filename)
  for line in in_file.readlines():
    if (not ('======' in line or 'VCS' in line)):
      values = line.split()
      info.append((values[0].strip(),
                  [('R_TOTAL_VC', values[1].strip()),
                   ('R_TOTAL_OBLIG', values[2].strip()),
                   ('R_UNVERIFIED_VC', values[3].strip()),
                   ('R_VALID_VC', values[4].strip()),
                   ('R_INVALID_VC', values[5].strip()),
                   ('R_FASTEST', values[6].strip()),
                   ('R_SLOWEST', values[7].strip()),
                   ('R_AVERAGE', values[8].strip()),
                   ('R_TOTAL_DP', values[9].strip()),
                   ('R_LEAP_TIME', values[10].strip()),
                   ('R_TOTAL_ANALYSIS', values[11].strip()),
                   ('R_DP_VC', [v.strip() for v in values[12].split('--')]),
                   ('R_DP_CALLS', [v.strip() for v in values[13].split('--')])]))
  in_file.close()
  return info


def lookup_history(history, name):
  try:
    return (dict(history)[name])
  except:
    return (dict())


def lookup_results(results, name):
  try:
    return [info for info in results if dict(info)['R_NAME'] == name][0]
  except:
    print '! No results for ' + name
    return []


def report_change(** args):
  if args['cond'] == 'equal':
    change('In example {}, key {} should be preserved, but historically was {} and now is {}'.format(args['name'], key_to_str(args['key']), args['hist_val'], args['curr_val']))
  if args['cond'] == 'zero':
    change('In example {}, key {} should be 0, but it is {}'.format(args['name'], key_to_str(args['key']), args['curr_val']))
  if args['cond'] == 'equal_curr':
    change('In example {}, key {} (with value {}) should be equal to key {} (with value {})'.format(args['name'], key_to_str(args['key1']), args['val1'], args['key2'], args['val2']))
  if args['cond'] == 'range_inc':
    change('In example {}, key {} used to be {} but now has increased to {}'.format(
              args['name'], key_to_str(args['key']), args['hist_val'], args['curr_val']))
  if args['cond'] == 'range_dec':
    change('In example {}, key {} used to be {} but now has decreased to {}'.format(
              args['name'], key_to_str(args['key']), args['hist_val'], args['curr_val']))



def compare_val(name, key, cond, history_vals, results, changes):
  try:
    hist_val = dict(history_vals)[key]
    curr_val = dict(results)[key]
    if cond == 'equal':
      if hist_val <> curr_val:
        report_change (name=name, key=key, cond=cond, hist_val=hist_val, curr_val=curr_val)
        changes.append({'type':'comp_val', 'name':name, 'key':key, 'cond':cond, 'hist_val':hist_val, 'curr_val':curr_val})
    if cond == 'zero':
      if curr_val <> '0':
        report_change (name=name, key=key, cond=cond, hist_val=hist_val, curr_val=curr_val)
        changes.append({'type':'comp_val', 'name':name, 'key':key, 'cond':cond, 'hist_val':hist_val, 'curr_val':curr_val})
  except:
    error ('Problem comparing values with key {}'.format(key_to_str(key)))


def compare_vals(name, key1, key2, cond, history_vals, results, changes):
  try:
    curr_val1 = dict(results)[key1]
    curr_val2 = dict(results)[key2]
    if cond == 'equal':
      if curr_val1 <> curr_val2:
        report_change (name=name, key1=key1, key2=key2, cond='equal_curr', val1=curr_val1, val2=curr_val2)
        changes.append({'type':'comp_vals', 'name':name, 'key1':key1, 'key2':key2, 'cond':cond, 'val1':val1, 'val2':val2})
  except:
    change('Problem comparing values between keys {} and {}'.format(key_to_str(key1), key_to_str(key2)))

  
def compare_range(name, key, history_vals, results, big_percent, small_percent, changes):
  try:
    hist_val = float(dict(history_vals)[key])
    curr_val = float(dict(results)[key])
    big_delta = (hist_val * big_percent)/100.0
    small_delta = (hist_val * small_percent)/100.0
    if hist_val < 0.1 and curr_val < 0.1:
      delta = 1.0
    elif hist_val < 1.0 and curr_val < 1.0:
      delta = small_delta
    else:
      delta = big_delta
    if curr_val > hist_val + delta:
      report_change (name=name, key=key, cond='range_inc', hist_val=hist_val, curr_val=curr_val)
      changes.append({'type':'comp_range', 'name':name, 'key':key, 'cond':cond, 'hist_val':hist_val, 'curr_val':curr_val})
    if curr_val < hist_val - delta:
      report_change (name=name, key=key, cond='range_dec', hist_val=hist_val, curr_val=curr_val)
      changes.append({'type':'comp_range', 'name':name, 'key':key, 'cond':cond, 'hist_val':hist_val, 'curr_val':curr_val})
  except:
    error('Problem comparing values with keys {}'.format(key_to_str(key)))


def compare_list(name, key, cond, history_vals, results, changes):
  try:
    hist_val = dict(history_vals)[key]
    curr_val = [dp+':'+n for (dp,n) in dict(results)[key]]
    if cond == 'equal':
      if set(hist_val) <> set(curr_val):
        change('In example {}, the elements under {} do not match. Historically it contained {} and now it contains {}'.format(name, key_to_str(key), hist_val, curr_val))
        changes.append({'type':'comp_list', 'name':name, 'key':key, 'cond':cond, 'hist_val':hist_val, 'curr_val':curr_val})
  except:
    error('Problem comparing values with keys {}'.format(key_to_str(key)))



# Main body
def test_deployment(verbose):
  changes = []
  head_msg ('Generating Leap')
  make = Popen(cmd_compile_leap, cwd=trunk_path)
  if make.wait() <> 0:
   error('Compiling Leap')

  head_msg ('Testing examples')
  delete_folder (testing_path)
  shutil.copytree(deployment_path, testing_path)
  create_folder (results_path)
  remove (join(testing_path,'all_examples.zip'))
  there_is_history = exists(history_path)
  summary_out = open (summary_path, 'w')
  write_summary_head (summary_out)

  if there_is_history:
    print 'History file found at "{}"'.format(history_path)
    history_values = read_summary_file(history_path)
  else:
    warning('No history file found. One will be created.')
    history_values = []

  for k in [d for d in list_folders(testing_path) if d <> result_folder]:
    k_path = join(testing_path, k)
    zips = list_files_of_type(k_path, '.zip')
    middle_msg(k)
    for f in zips:
      print 'Unzipping example file {} ...'.format(f)
      unzip (k_path, f)

    # We operate over each example
    examples = list_folders(k_path)
    results = []
    for ex in examples:
      # Load the script information
      print_short_separator()
      print ('Analyzing example {}:{}...'.format(k,ex))
      example_path = join(k_path,ex)
      scripts = list_files_of_type (example_path,'.sh')
      for sh in scripts:
        if k == 'safety':
          print 'For example {}, analyzing script {} ...'.format(ex, sh)
          sh_path = join(example_path, sh)
          sh_input = open(sh_path)
          sh_lines = sh_input.readlines()
          sh_input.close()
          if not verbose:
            sh_lines_str = ''.join(sh_lines)
            optimal_sh_lines = sh_lines_str.replace('-v 1','-v 0')
            sh_out = open(sh_path, 'w')
            sh_out.seek(0)
            sh_out.truncate()
            sh_out.write(optimal_sh_lines)
            sh_out.close()

          graph_info = [g for g in sh_lines if 'graph' in g]
          if len(graph_info) > 1:
            error ('More than one graph file defined in file ' + sh_input)
          graph_file = graph_info[0].split('=')[1].strip()
          print 'Graph information located in ' + graph_file
          graph_path = join(example_path, graph_file)
          graph_in = open(graph_path)
          graph_lines = graph_in.readlines()
          graph_in.close()
          cases = parse_graph_cases(graph_lines)
          case_counter = 1
          for case in cases:
            print_info ('Analyzing case {} of {}: {}...'.format(case_counter, len(cases), case.name))
            case_counter += 1
            test_graph = open(graph_path, 'w')
            test_graph.write (case.content)
            test_graph.close()
            result = run_script (sh_path, k, ex, case.name)
            write_summary_line (summary_out, result)
            results.append(result)
            # Compare with historic values
            if there_is_history:
              vals = lookup_history(history_values, (k + '_' + ex + '_' + case.name))
              if vals == dict():
                error ('No historic information found for example {}'.format(case.name))
              else:
                compare_val(case.name, 'R_TOTAL_VC', 'equal', vals, result, changes)
                compare_val(case.name, 'R_TOTAL_OBLIG', 'equal', vals, result, changes)
                compare_val(case.name, 'R_UNVERIFIED_VC', 'equal', vals, result, changes)
                compare_val(case.name, 'R_INVALID_VC', 'equal', vals, result, changes)
                compare_val(case.name, 'R_VALID_VC', 'equal', vals, result, changes)
                compare_val(case.name, 'R_UNVERIFIED_VC', 'zero', vals, result, changes)
                compare_val(case.name, 'R_INVALID_VC', 'zero', vals, result, changes)
                compare_vals(case.name, 'R_TOTAL_VC', 'R_VALID_VC', 'equal', vals, result, changes)
                compare_range(case.name, 'R_FASTEST', vals, result, 10.0, 20.0, changes)
                compare_range(case.name, 'R_SLOWEST', vals, result, 10.0, 20.0, changes)
                compare_range(case.name, 'R_AVERAGE', vals, result, 10.0, 20.0, changes)
                compare_range(case.name, 'R_TOTAL_DP', vals, result, 10.0, 20.0, changes)
                compare_range(case.name, 'R_LEAP_TIME', vals, result, 10.0, 20.0, changes)
                compare_range(case.name, 'R_TOTAL_ANALYSIS', vals, result, 10.0, 20.0, changes)
                compare_list(case.name, 'R_DP_VC', 'equal', vals, result, changes)
                compare_list(case.name, 'R_DP_CALLS', 'equal', vals, result, changes)
          orig_graph_out = open(graph_path, 'w')
          orig_graph_out.writelines(graph_lines)
          orig_graph_out.close()
        elif k == 'liveness':
          print 'Liveness verification not implemented yet'
    

  summary_out.close()
  print_med_separator()
  print ('{} Changes detected'.format(len(changes)))
  if not there_is_history:
    shutil.copyfile(summary_path, history_path)
    warning ('New history file {} created. No testing has been performed.'.format(history_path))
  print_separator()


def deploy(examples):
  head_msg ('Deploying examples')
  clean_examples(examples)
  create_folder(deployment_path)
  all_examples_path = join(deployment_path, all_examples)
  create_folder(all_examples_path)

  for k in examples.keys():
    k_path = join(current_path, k)
    deployment_k_path = join(deployment_path, k)
    deployment_all_examples_k_path = join(all_examples_path, k)
    create_folder(deployment_k_path)
    create_folder(deployment_all_examples_k_path)
    
    for ex in examples[k]:
      ex_path = join(k_path, ex)
      print 'Creating zip file for {}:{} ...'.format(k,ex)
      zip(k_path, ex, join(deployment_k_path, ex))
      shutil.copytree(ex_path, join(deployment_all_examples_k_path, ex))
  zip(deployment_path, all_examples, all_examples)
  shutil.rmtree(all_examples_path)
  print 'Examples will be deployed to "{}"'.format(deployment_path)
  


def main(argv):
  parser = argparse.ArgumentParser(description='Script to deliver and test examples')
  parser.add_argument('examples', metavar='ex_file', type=str,
                     help='the file containing the list of examples to be delivered')
  parser.add_argument('-test', action='store_true', default=False,
                        help='runs the examples and compare the results against historic values')
  parser.add_argument('-clean', action='store_true', default=False,
                        help='deletes all temporary vcs, swap files, testing and deployment folders')
  parser.add_argument('-deploy', action='store_true', default=False,
                        help='deploys the examples so they can be published later')
  parser.add_argument('-verbose', action='store_true', default=False,
                        help='runs the examples in verbose mode, outputting all details')

  args = parser.parse_args()

  old_env_path = update_env_path()
  examples = dict()
  if args.examples.strip() <> '':
    examples_in = open(join(current_path, args.examples))
    curr_cat = ''
    for word in [w.strip() for w in examples_in.readlines() if not w.strip().startswith('//')]:
      if ':' in word:
        curr_cat = word.strip(' :')
        examples[curr_cat] = []
      elif word <> '':
        examples[curr_cat].append(word)
    examples_in.close()

  if args.clean or args.deploy:
    clean_examples(examples)

  if args.deploy:
    deploy(examples)

  if args.test or args.deploy:
    test_deployment(args.verbose)

  environ['PATH'] = old_env_path


if __name__ == "__main__":
   main(sys.argv[1:])
