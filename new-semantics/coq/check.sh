coqchk -silent -o -R basics Basics -R equivalence Without_events -R events With_events basics/*.vo equivalence/*.vo events/*.vo
