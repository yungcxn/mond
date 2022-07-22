'''
installation script for mondc compiler
'''
import os.path
from distutils.dir_util import copy_tree

print("installing mondc...")
print()

localpath = os.path.abspath("../mondlibs")

print("current libraries are located at " + localpath)

libloc = "mondlibs"
from sys import platform
if platform == "linux" or platform == "linux2":
    libloc = "/usr/local/include/" + libloc
elif platform == "darwin":
    libloc = "/usr/local/include/" + libloc
elif platform == "win32":
    libloc = "C:/include/" + libloc

print("copying libraries to... " + libloc)

copy_tree(localpath, libloc)