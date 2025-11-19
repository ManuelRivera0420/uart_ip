# Definitions #
import serial
import numpy as np
import struct
import time
from random import randint

try:
	ser = serial.Serial('/dev/ttyUSB0',baudrate=9600)
	print("Succesfully connected to uart slave")
except:
	print("Could not connect to uart slave")

def write_mem(addr,data):
	COMMAND = 0
	v = struct.pack('B', COMMAND)
	ser.write(v)
	v = struct.pack('I',addr)
	ser.write(v)
	v = struct.pack('I',data)
	ser.write(v)
	print("wrote " + "{:08X}".format(data) )

def read_mem(addr):
	COMMAND = 1
	v = struct.pack('B', COMMAND)
	ser.write(v)
	v = struct.pack('I',addr)
	ser.write(v)
	v = struct.pack('I',0)
	ser.write(v)
	while(ser.in_waiting < 4):()
	val = ser.read(4)
	data_received = int.from_bytes(val, "little")
	print("read {:08X}".format(data_received))

COMMAND = 155
v = struct.pack('B', COMMAND)
ser.write(v)

#for i in range(0,10): # Do 10 random data writes to address 0-9
#	write_mem(i,randint(0,100))
#for i in range(0,10): # Do 10 reads to address 0-9
#	read_mem(i)
