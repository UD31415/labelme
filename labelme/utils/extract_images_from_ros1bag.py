#!/usr/bin/env python3

import os
import argparse
import numpy as np

from pathlib import Path
import pprint

from rosbags.highlevel import AnyReader
#import cv2 as cv


def parse_cli_args():
    parser = argparse.ArgumentParser(
        description="Extract data from requested topics in an mcap recording and save them to the filesystem."
    )
    parser.add_argument(
        "-i",
        "--input",
        type=str,
        help="Input bag path (folder or filepath) to read from",
        #default="C:\\Data\\Safety\\AGV\\240__static_hall_carpet_fluorescent.bag",
        #default=r"C:\Data\Safety\AGV\12_static_both_prj_covered_hall_carpet.bag",
        default=r"C:\Data\Safety\AGV\12_in_motion_both_prj_hall_ceramic_tile_sun.bag",
        required=False,
    )
    parser.add_argument(
        "-o",
        "--output",
        type=str,
        help="Output path for serialized data",
        #default="C:\\Data\\Safety\\AGV\\240__static_hall_carpet_fluorescent",
        #default=r"C:\\Data\\Safety\\AGV\\12_static_both_prj_covered_hall_carpet",
        default=r"C:\\Data\\Safety\\AGV",
        required=False,
    )
    parser.add_argument(
        "-t",
        "--topics",
        metavar="T",
        type=str,
        nargs="+",
        help="List of topics to be serialized",
        default =  '/device_0/sensor_0/Infrared_1/image/data', #'/device_0/sensor_0/Depth_0/image/data',
        required=False,
    )
    args = parser.parse_args()
    return args

def get_friendly_topic_name(topic):
    ''' Generates a topic name that doesn't contain forward slashes '''
    return topic.replace("/", "_")[1:]

def print_topics():
    args = parse_cli_args()

    topics = []
    with AnyReader([Path(args.input)]) as reader:
        connections = [x for x in reader.connections]        
        for connection, _, rawdata in reader.messages(connections=connections):
            topics.append(connection.topic)

    pprint.pprint(set(topics))
    return

def extract_from_rosbag(args, filepath):
    print(f"Extracting rosbag {filepath}")
    with AnyReader([Path(filepath)]) as reader:
        connections = [x for x in reader.connections if x.topic in args.topics]
        for connection, _, rawdata in reader.messages(connections=connections):
            rosbag_topics_output_path = os.path.join(args.output, os.path.basename(filepath)[:-4], get_friendly_topic_name(connection.topic))
            os.makedirs(rosbag_topics_output_path, exist_ok=True)
            if "image_data" in rosbag_topics_output_path:
                msg = reader.deserialize(rawdata[:-4], connection.msgtype)
                prefix = connection.msgtype.split('/')[-1].lower()
                timestamp = msg.header.stamp.sec * 1_000_000_000 + msg.header.stamp.nanosec
                separator = "_"
                resolution = f"{msg.width}x{msg.height}"
                encoding = msg.encoding.lower()
                step = f"step_{msg.step}"
                ext = ".bin"

                of = os.path.join(rosbag_topics_output_path, f"{prefix}{separator}{timestamp}{separator}{resolution}{separator}{step}{separator}{encoding}{ext}")
                with open(of, "w+b") as f:
                    f.write(msg.data)

            elif "info_camera_info" in rosbag_topics_output_path:
                msg = reader.deserialize(rawdata, connection.msgtype)
                prefix = "info"
                separator = "_"
                ext = ".txt"

                of = os.path.join(rosbag_topics_output_path, f"{prefix}{ext}")
                with open(of, "w") as f:
                    for i in range(9):
                        f.write(f"K[{i}]={msg.K[i]}\n")
            
            else:
                print(f"I don't know how to parse topic: {connection.topic}")

def read_bin_file(fname, Size=(640, 480), bpp=16):
    """Reads a binary file and returns it as a NumPy array.

    Args:
        fname (str): The name of the file to read.
        Size (tuple): The size of the image (width, height).
        bpp (int): The number of bits per pixel.

    Returns:
        np.ndarray: The image data as a NumPy array.
    """

    try:
        f = open(fname, 'rb')
    except IOError:
        print("Error: Could not open file", fname)
        return None

    if bpp > 32:
        dtype = np.uint64
    elif bpp > 16:
        dtype = np.uint32
    elif bpp > 8:
        dtype = np.uint16
    else:
        dtype = np.uint8

    A = np.fromfile(f, dtype=dtype, count=Size[0] * Size[1]).reshape(Size[::-1])

    if bpp > 8:
        A = np.bitwise_and(A, 2**bpp - 1)

    f.close()

    return A

def extract_bag():
    
    args = parse_cli_args()

    inputPath = args.input
    if os.path.isdir(inputPath):
        for name in os.listdir(inputPath):
            extract_from_rosbag(args, os.path.join(inputPath, name))
    else:
        extract_from_rosbag(args, args.input)

# def test_read_bin():
#     "test bin file reading"
#     fpath       = r"C:\Data\Safety\AGV\240__static_hall_carpet_fluorescent\240__static_hall_carpet_fluorescent\device_0_sensor_0_Infrared_1_image_data\image_1727253111630055904_1280x720_step_1280_8uc1.bin"
#     fsize       = (1280,720)
#     fbpp        = 8
#     img_array   = read_bin_file(fpath,fsize,fbpp)
#     vis         = cv.cvtColor(img_array, cv.COLOR_GRAY2RGB)
#     cv.imshow('Infrared', vis)


#     fpath       = r"C:\Data\Safety\AGV\240__static_hall_carpet_fluorescent\240__static_hall_carpet_fluorescent\device_0_sensor_0_Depth_0_image_data\image_1727253111694310904_1280x720_step_2560_mono16.bin"
#     fsize       = (1280,720)
#     fbpp        = 16
#     img_array   = read_bin_file(fpath,fsize,fbpp)
#     depth_scaled        = cv.convertScaleAbs(img_array, alpha=0.03)
#     depth_colormap      = cv.applyColorMap(depth_scaled, cv.COLORMAP_JET)

#     cv.imshow('Depth', depth_colormap)
#     ch  = cv.waitKey()

# def read_and_show_infrared():
#     "multiple bin file reading of the infrared data"
#     fpath       = r"C:\Data\Safety\AGV\12_in_motion_both_prj_covered_hall_carpet\device_0_sensor_0_Infrared_1_image_data"
#     fpath       = r"C:\Data\Safety\AGV\12_in_motion_no_prj_covered_hall_carpet\device_0_sensor_0_Infrared_1_image_data"
#     fpath       = r"C:\Data\Safety\AGV\12_in_motion_both_prj_hall_ceramic_tile_sun\device_0_sensor_0_Infrared_1_image_data"
#     fpath       = r"C:\Data\Safety\AGV\12_in_motion_no_prj_hall_ceramic_tile_sun\device_0_sensor_0_Infrared_1_image_data"
#     fpath       = r'C:\Users\udubin\Documents\Projects\Safety\data\laser_classifier\small\on'
#     fsize       = (1280,720)
#     fbpp        = 8
    

#     # Filter for files with specific extensions (optional)
#     files       = os.listdir(fpath)
#     file_extensions = [".bin"]
#     filtered_files = [file for file in files if os.path.isfile(os.path.join(fpath, file)) and file.endswith(tuple(file_extensions))]

#     # Iterate over files and process them
#     for file in filtered_files:
#         file_path   = os.path.join(fpath, file)
#         img_array   = read_bin_file(file_path,fsize,fbpp)
#         vis         = cv.cvtColor(img_array, cv.COLOR_GRAY2RGB)
#         cv.imshow('Infrared q-quit', vis)
#         print(file_path.split('\\')[-1])
#         ch  = cv.waitKey(100)
#         if ch == 27 or ch == ord('q'):
#             break  
#         elif ch == ord(' '):
#             print('Pause ....')
#             ch  = cv.waitKey()


#     print('Done')



if __name__ == '__main__':
    #extract_bag()
    #print_topics()
    #test_read_bin()
    read_and_show_infrared()
