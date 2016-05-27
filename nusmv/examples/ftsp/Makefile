all: sync async
sync:
	for N in 1 2 3 4 5 6; do \
		m4 -DN=$$N -DDELTA=1 ftsp-incr-sync.m4> generated/ftsp-incr-sync-$$N.smv ; \
	done
async:
	for N in 1 2 3 4 5; do \
		m4 -DN=$$N -DDELTA=1 ftsp-incr.m4> generated/ftsp-incr-$$N.smv ; \
	done
