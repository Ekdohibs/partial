from constants import *

def add_to_env(env, name, value):
    return ((name, value), env)

def env_find(env, name):
    while env != None:
        if env[0][0] == name:
            return env[0][1]
        env = env[1]
    raise Exception('Name not found in env : "'+name+'"')

def make_env(l):
    env = None
    for (name, value) in l:
        env = add_to_env(env, name, value)
    return env
