# Symmetric Superpolynomials module for SAGE
Superpartitions, superpolynomial ring and superspace in SAGE.

This is intended to be used with the Compendium of results on superpolynomials which will be published on arXiv in early april.

## Instructions
### Requirements
- Sage 8.1+

### Installing Sage
Please follow the instructions found at 
http://doc.sagemath.org/html/en/installation/index.html

If you are familiar with bittorent, this download option is recommended. We also recommend to use the binaries.

### Installing the module
If you are familiar with git, simply clone this repository:

`git clone https://github.com/LAV42/SageCompendium.git`

If you are not click the green "Clone or download" button on the top right of the files list and click Download ZIP. 
Then extract the zip files in a directory of your choice. 

Once this is done, open up the terminal and type

`sage -n jupyter`

this should open a Jupyter session in your browser. From there, you should see a file manager.
Navigate to the directory where you extacted the zip file (or cloned the repository).

Click on SageCompendium.ipynb

The jupyter notebook should get you started. To execute a cell, depending on the platform, use Shift+Enter, Ctrl+Enter or click the black play button in the tool bar. 

### Using from the terminal
Within the terminal, navigate where you extracted SageCompendium. From there type `sage` to start a sage session. To load the module you can simply do the following

`load('all.py')`
