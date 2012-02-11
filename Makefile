
all:
	agda -i ~/installs/agda-stdlib/lib-0.6/src/ -i . -c TypeCheck.agda

clean:
	rm -rf MAlonzo
	rm -f *.agdai *.hi *.o
	rm TypeCheck
