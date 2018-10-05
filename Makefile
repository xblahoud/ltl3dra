# LTL3DRA - Version 0.1 - August 2013

# Written by Denis Oddoux, LIAFA, France                                 
# Copyright (c) 2001  Denis Oddoux                                       
# Modified by Paul Gastin, LSV, France                                   
# Copyright (c) 2007  Paul Gastin                                        
# Modified by Tomas Babiak, FI MU, Brno, Czech Republic                  
# Copyright (c) 2012  Tomas Babiak   
# Modified by Tomas Babiak and Frantisek Blahoudek, Brno, Czech Republic
# Copyright (c) 2013  Tomas Babiak and Frantisek Blahoudek                                   
#                                                                        
# This program is free software; you can redistribute it and/or modify   
# it under the terms of the GNU General Public License as published by   
# the Free Software Foundation; either version 2 of the License, or      
# (at your option) any later version.                                    
#                                                                        
# This program is distributed in the hope that it will be useful,        
# but WITHOUT ANY WARRANTY; without even the implied warranty of         
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          
# GNU General Public License for more details.                           
#                                                                        
# You should have received a copy of the GNU General Public License      
# along with this program; if not, write to the Free Software            
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
#                                                                        
# Based on the translation algorithm by Gastin and Oddoux,               
# presented at the 13th International Conference on Computer Aided       
# Verification, CAV 2001, Paris, France.                                 
# Proceedings - LNCS 2102, pp. 53-65                                     
#                                                                        
# and on paper by                                        
# T. Babiak, M. Kretinsky, V. Rehak, and J. Strejcek,                    
# LTL to Buchi Automata Translation: Fast and More Deterministic         
# presented at the 18th International Conference on Tools and            
# Algorithms for the Construction and Analysis of Systems (TACAS 2012)   
#
# The translation to deterministic Rabin automata is based on paper by
# T. Babiak, F. Blahoudek, M. Kretinsky, and J. Strejcek
# Effective Translation of LTL to Deterministic Rabin Automata: Beyond the (F,G)-Fragment (2013)
# In 11th International Symposium on Automated Technology for Verification and Analysis (ATVA 2013)

# Set PATH to "bdd.h" BuDDy file.
BUDDY_INCLUDE=../buddy/src/
# Set PATH to "libbdd.a" BuDDy file.
BUDDY_LIB=../buddy/src/.libs/

# to obtain BuDDy you can run (with admin privileges):
# $ make install_buddy
# which installs buddy into the default locations and
# then you do not need to set the variables at all.

CC=g++
CXX=g++
CPPFLAGS=-O3 -DNXT -I$(BUDDY_INCLUDE)

LTL3DRA=	parse.o lex.o main.o trans.o buchi.o cset.o set.o dra.o ra.o\
	mem.o rewrt.o cache.o alternating.o generalized.o optim.o

all: ltl3dra

ltl3dra:$(LTL3DRA)
	$(CXX) $(CPPFLAGS) -o ltl3dra $(LTL3DRA) -L$(BUDDY_LIB) -lbdd

$(LTL3DRA): ltl3dra.h dra.h ra.h

clean:
	rm -f ltl3dra *.o

# Makes ltl3dra available on your computer. Need administrative priviliges
install: ltl3dra
	cp ltl3dra /usr/local/bin
	cp LICENSE README /usr/local/share/doc/ltl3dra

install_buddy:
	bash install_buddy.sh
