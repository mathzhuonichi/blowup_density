.PHONY: check test test-mutations tasks paper snapshot

check:
	python3 experiments/check_formalization_plan.py --check
	python3 experiments/check_contracts.py
	python3 experiments/test_contract_policy.py
	python3 experiments/check_work_queue.py

test:
	lake -d verification test

test-mutations:
	python3 experiments/test_contract_mutations.py

tasks:
	python3 experiments/tasks.py list --ready

paper:
	$(MAKE) -C paper
	python3 experiments/check_manuscript.py

snapshot:
	python3 experiments/check_formalization_plan.py --snapshot --check
