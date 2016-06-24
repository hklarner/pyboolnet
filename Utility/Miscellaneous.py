

try:
    # Python 2.x
    import ConfigParser as configparser
    
except ImportError:
    # Python 3.x
    import configparser

myconfigparser = configparser
