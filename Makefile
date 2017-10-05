all: enigma.vo

enigma.vo: enigma.v permutations.vo alphabet.vo bijections.vo utils.vo
	coqc $<

permutations.vo: permutations.v alphabet.vo utils.vo
	coqc $<

alphabet.vo: alphabet.v
	coqc $<

bijections.vo: bijections.v
	coqc $<

utils.vo: utils.v
	coqc $<

clean:
	rm -f *.vo

.PHONY: all cleanp
