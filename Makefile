.PHONY: check test test-mutations paper clean

check:
	python3 experiments/check_formalization_plan.py --check
	python3 experiments/check_contracts.py --summary
	python3 experiments/test_contract_policy.py

test:
	lake -d verification test

test-mutations:
	python3 experiments/test_contract_mutations.py

paper:
	$(MAKE) -C paper readers

clean:
	$(MAKE) -C paper clean
