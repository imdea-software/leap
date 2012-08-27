#######################################################################
#
# Runs some ../examples for prog2fts and numinv
#
#######################################################################


## Abstract philosophers
# echo "Running '../numinv ../examples/prg/philosophers_abstract.prg --iterate --show_invariants --show_file_info --use_labels --inv_file ../examples/invs/philosopher_abstract.inv'";
# ../numinv --show_statistic_info ../examples/prg/philosophers_abstract.prg --hide_problem;
# time ../numinv ../examples/prg/philosophers_abstract.prg --iterate --show_invariants --show_file_info --use_labels --inv_file ../examples/invs/philosophers_abstract.inv > ../examples/out/philosophers_abstract.out;


## 2 Philosophers
# echo "Running '../numinv ../examples/prg/philosopher2.prg --iterate --show_invariants --show_file_info --inv_file ../examples/invs/philosopher2.inv'";
# ../numinv --show_statistic_info ../examples/prg/philosopher2.prg --hide_problem;
# time ../numinv ../examples/prg/philosopher2.prg --iterate --show_invariants --show_file_info --inv_file ../examples/invs/philosopher2.inv > ../examples/out/philosopher2.out;


## Minticket
# echo "Running '../numinv ../examples/prg/ticketint.prg --iterate --show_invariants --show_file_info --inv_file ../examples/invs/ticketint.inv'";
# ../numinv --show_statistic_info ../examples/prg/ticketint.prg --hide_problem;
# time ../numinv ../examples/prg/ticketint.prg --iterate --show_invariants --show_file_info --inv_file ../examples/invs/ticketint.inv > ../examples/out/ticketint.out;


## Simple 2-index counter (DOES NOT STOP)
# echo "Running '../numinv ../examples/prg/counter.prg --iterate --show_invariants --show_file_info --compose 2 --inv_file ../examples/invs/counter2.inv'";
# ../numinv --show_statistic_info ../examples/prg/counter.prg --compose 2 --hide_problem;
# time ../numinv ../examples/prg/counter.prg --iterate --show_invariants --show_file_info --compose 2 --inv_file ../examples/invs/counter2.inv > ../examples/out/counter2.out;


## Simple 2-index counter (WIDENING AFTER 8)
# echo "Running '../numinv ../examples/prg/counter.prg --iterate --show_invariants --show_file_info --compose 2 --widening_after 8 --inv_file ../examples/invs/counter2_widening8.inv'";
# ../numinv --show_statistic_info ../examples/prg/counter.prg --compose 2 --hide_problem;
# time ../numinv ../examples/prg/counter.prg --iterate --show_invariants --show_file_info --compose 2 --widening_after 8 --inv_file ../examples/invs/counter2_widening8.inv > ../examples/out/counter2_widening8.out;


## Minticket with 2-index
# echo "Running '../numinv ../examples/prg/ticketint.prg --iterate --show_invariants --show_file_info --compose 2 --inv_file ../examples/invs/ticketint2.inv'";
# ../numinv --show_statistic_info ../examples/prg/ticketint.prg --compose 2 --hide_problem;
# time ../numinv ../examples/prg/ticketint.prg --iterate --show_invariants --show_file_info --compose 2 --inv_file ../examples/invs/ticketint2.inv > ../examples/out/ticketint2.out;


## Work stealing 
  echo "Running '../numinv ../examples/prg/workstealing.prg --iterate --show_invariants --show_file_info --inv_file ../examples/invs/workstealing.inv'";
  ../numinv --show_statistic_info ../examples/prg/workstealing.prg --hide_problem;
  time ../numinv ../examples/prg/workstealing.prg --iterate --show_invariants --show_file_info --inv_file ../examples/invs/workstealing.inv > ../examples/out/workstealing.out;


## Work stealing 2-index
  echo "Running '../numinv ../examples/prg/workstealing.prg --iterate --show_invariants --show_file_info --compose 2 --inv_file ../examples/invs/workstealing2.inv'";
  ../numinv --show_statistic_info ../examples/prg/workstealing.prg --compose 2 --hide_problem;
  time ../numinv ../examples/prg/workstealing.prg --iterate --show_invariants --show_file_info --compose 2 --inv_file ../examples/invs/workstealing2.inv > ../examples/out/workstealing2.out;

