.PHONY: all pdf build build-lib test clean run \
        bench-build bench-quick bench-full \
        bench-summarize-quick bench-summarize-full \
        bench-quick-report bench-full-report \
        bench-clean bench-check clean-junk

TEXDIR := tex
MAIN := KHora

BENCH_RAW_DIR := benchmarks/results/raw
BENCH_PLOT_DIR := benchmarks/results/plots

all: pdf build

pdf:
	latexmk -pdf -output-directory=$(TEXDIR) -interaction=nonstopmode $(TEXDIR)/$(MAIN).tex

build:
	stack build

build-lib:
	stack build KHora:lib

run:
	@echo "No default executable is built in the core package."
	@echo "Use 'make bench-quick-report' for benchmarks or 'stack ghci' for interactive use."

test:
	@echo "No test suite is currently configured."

clean:
	stack clean
	latexmk -C -output-directory=$(TEXDIR) $(TEXDIR)/$(MAIN).tex || true
	rm -f texput.log
	rm -f $(TEXDIR)/*.aux $(TEXDIR)/*.log $(TEXDIR)/*.out $(TEXDIR)/*.snm $(TEXDIR)/*.toc $(TEXDIR)/*.vrb $(TEXDIR)/*.nav $(TEXDIR)/*.synctex.gz $(TEXDIR)/*.blg $(TEXDIR)/*.bbl $(TEXDIR)/*.fdb_latexmk $(TEXDIR)/*.fls $(TEXDIR)/*.ind $(TEXDIR)/*.idx $(TEXDIR)/*.ilg $(TEXDIR)/*.bcf $(TEXDIR)/*.run.xml $(TEXDIR)/*.xdv

clean-junk:
	rm -rf __MACOSX
	find . -name "._*" -delete

bench-build:
	stack build KHora:exe:khora-bench

bench-quick: bench-build
	mkdir -p $(BENCH_RAW_DIR) $(BENCH_PLOT_DIR)
	stack exec khora-bench -- --quick

bench-full: bench-build
	mkdir -p $(BENCH_RAW_DIR) $(BENCH_PLOT_DIR)
	stack exec khora-bench -- --full

bench-summarize-quick:
	python3 benchmarks/scripts/summarize_results.py $(BENCH_RAW_DIR)/quick.csv

bench-summarize-full:
	python3 benchmarks/scripts/summarize_results.py $(BENCH_RAW_DIR)/full.csv

bench-quick-report: bench-quick bench-summarize-quick

bench-full-report: bench-full bench-summarize-full

bench-clean:
	rm -f $(BENCH_RAW_DIR)/*.csv
	rm -f $(BENCH_PLOT_DIR)/*.png
	rm -f $(BENCH_PLOT_DIR)/*.csv
	mkdir -p $(BENCH_RAW_DIR) $(BENCH_PLOT_DIR)
	touch $(BENCH_RAW_DIR)/.gitkeep
	touch $(BENCH_PLOT_DIR)/.gitkeep

bench-check:
	stack build
	$(MAKE) bench-quick-report

.PHONY: dev dev-build dev-clean dev-bench dev-verify dev-plot dev-open

DEV_CSV := benchmarks/results/raw/quick.csv
DEV_PLOTS := benchmarks/results/plots

dev: dev-build dev-clean dev-bench dev-verify dev-plot
	@echo ""
	@echo "[OK] Build + benchmark + verification + plots finished."
	@echo "CSV:   $(DEV_CSV)"
	@echo "Plots: $(DEV_PLOTS)"

dev-build:
	stack build

dev-clean:
	rm -f benchmarks/results/raw/*.csv
	rm -f benchmarks/results/plots/*.png
	rm -f benchmarks/results/plots/*.csv
	mkdir -p benchmarks/results/raw benchmarks/results/plots
	touch benchmarks/results/raw/.gitkeep
	touch benchmarks/results/plots/.gitkeep

dev-bench:
	stack exec khora-bench -- --quick

dev-verify:
	stack exec khora-check-basic -- $(DEV_CSV)
	stack exec khora-check-intermediate -- $(DEV_CSV)
	stack exec khora-check-regular -- $(DEV_CSV)
	stack exec khora-check-budget -- $(DEV_CSV)
	stack exec khora-check-all -- $(DEV_CSV)

dev-plot:
	python3 benchmarks/scripts/summarize_results.py $(DEV_CSV)

dev-open:
	open $(DEV_PLOTS)