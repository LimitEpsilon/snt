coqchk -silent -o -R basics Basics -R sim Without_events -R events With_events -R basics/*.vo sim/*.vo events/*.vo
