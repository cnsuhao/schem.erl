.SUFFIXES: .erl .beam .xrl .yrl

.erl.beam:
	erlc -W $<

ERL = erl -boot start_clean

MODS = lfe_io lfe_scan lfe_parse schem

all: compile

compile:${MODS:%=%.beam}

clean:
	rm -rf *.beam erl_crash.dump
