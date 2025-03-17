all: libsymdict.so

libsymdict.so:
	$(CXX) $(CXXFLAGS) -D_FORTIFY_SOURCE=2 -O3 -fPIC -shared -g -I../ -I./ symdict.cpp -o libsymdict.so

clean:
	rm -rf libsymdict.so

