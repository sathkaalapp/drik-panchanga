#! /usr/bin/env python

# panchanga.py -- routines for computing tithi, vara, etc.
#
# Copyright (C) 2013 Satish BD  <bdsatish@gmail.com>
# Downloaded from https://github.com/bdsatish/drik-panchanga
#
# This file is part of the "drik-panchanga" Python library
# for computing Hindu luni-solar calendar based on the Swiss ephemeris
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

"""
Use Swiss ephemeris to calculate tithi, nakshatra, etc.
"""

from __future__ import division
from math import floor, ceil
from collections import namedtuple as struct
import swisseph as swe
import numpy as np
import json as json
from operator import sub
import getopt
import sys
import optparse
from pytz import timezone, utc
from datetime import datetime


Date = struct('Date', ['year', 'month', 'day'])
Place = struct('Location', ['latitude', 'longitude', 'timezone'])

SUB_C_E_USAGE_STR    = "Couldn't find proper input value for -e option, provide either m or y."
SUB_C_IM_USAGE_STR   = "option -i requires tithis in range 1-30 and -m requires months in range 1-12"
SUB_C_D_USAGE_STR    = "option (-d) requires proper date in DD-MM-YYYY format"
SUB_C_L_USAGE_STR    = "option (-l) requires proper location name, please get proper location using -L option"
MAIN_OPT_AL_USE_STR  =  "python3 panchanga.py -L [location name] [-v]"
MAIN_OPT_AC_USE_STR  =  "python3 panchanga.py -C [-l location name] | [-x latitude, -y longitude -t timezone] -d DD-MM-YYYY [-e [m|y]] [-v]"
MAIN_OPT_AC_USE_STR1 =  "python3 panchanga.py -C [-l location name] | [-x latitude, -y longitude -t timezone] -d DD-MM-YYYY -i <1-30>  -m <1-12> [-v]"
MAIN_OPT_C_USAGE_STR =  "option(-C) requires date in -d DD-MM-YYYY and [ [-l location name] or [-x latitude, -y longitude -t timezone]] [-e [m|y]]"
MAIN_OPT_L_USAGE_STR =  "option(-L) displays list of all predefined locations,  -v to display latitude, longitude locations and timezone"
MAIN_OPT_USAGE_GUIDE =  "Examples:"
MAIN_OPT_USAGE_EX1   =  "python3 panchanga.py -L                            # lists currently available locations"
MAIN_OPT_USAGE_EX2   =  "python3 panchanga.py -L Tirupati                   # Is Tirupati part of current available list"
MAIN_OPT_USAGE_EX2   =  "python3 panchanga.py -L Tirupati -v                # if Tirupati is part of availabe list, then display its latitude and logitude"
MAIN_OPT_USAGE_EX3   =  "python3 panchanga.py -C -l Tirupati -d 10-11-2020  # Displays Tirupati's detailed panchang info of given date"
MAIN_OPT_USAGE_EX4   =  "python3 panchanga.py -C -x 13.650  -y 79.41667 -t 'Asia/Kolkata' -d 10-11-2020  # Displays given location's detailed panchang info of given date"
MAIN_OPT_USAGE_EX5   =  "python3 panchanga.py -C -l Tirupati -d 10-11-2020 -e m  # Displays Tirupati's detailed panchang info of given telugu month"
MAIN_OPT_USAGE_EX6   =  "python3 panchanga.py -C -l Tirupati -d 10-11-2020 -e y  # Displays Tirupati's detailed panchang info of given telugu year"
MAIN_OPT_USAGE_EX7   =  "python3 panchanga.py -C -l Tirupati -d 10-11-2020 -i 10 -m 2  # Displays Tirupati's next occurance of given tithi and masam in gregorian dates"
MAIN_OPT_USAGE_EX8   =  "python3 panchanga.py -C -x 13.650  -y 79.41667 -t 'Asia/Kolkata' -d 10-11-2020 -i 5 -m 10  # Displays given location's detailed panchang info of given tithi and masam"

MAIN_OPT_ALL_USE_STR = MAIN_OPT_AL_USE_STR + "\n" + MAIN_OPT_AC_USE_STR + "\n" +  MAIN_OPT_AC_USE_STR1
MAIN_OPT_USAGE_EXM = MAIN_OPT_USAGE_EX1 + "\n" + MAIN_OPT_USAGE_EX2 + "\n" + MAIN_OPT_USAGE_EX3 + "\n" + MAIN_OPT_USAGE_EX4 + "\n" + MAIN_OPT_USAGE_EX5 + "\n" + MAIN_OPT_USAGE_EX6 + "\n" + MAIN_OPT_USAGE_EX7 + "\n" + MAIN_OPT_USAGE_EX8
MAIN_USAGE_STR = MAIN_OPT_ALL_USE_STR + "\n" + MAIN_OPT_USAGE_GUIDE + "\n" + MAIN_OPT_USAGE_EXM

format_time = lambda t: "%02d:%02d:%02d" % (t[0], t[1], t[2])
format_date = lambda t: "%02d-%02d-%02d" % (t[2], t[1], t[0])
format_date1 = lambda t: "%02d-%02d-%04d" % (t[2], t[1], t[0])
# Convert 23d 30' 30" to 23.508333 degrees
from_dms = lambda degs, mins, secs: degs + mins/60 + secs/3600

# the inverse
def to_dms(deg):
  d = int(deg)
  mins = (deg - d) * 60
  m = int(mins)
  s = int(round((mins - m) * 60))
  return [d % 24, m, s]

def unwrap_angles(angles):
  """Add 360 to those elements in the input list so that
     all elements are sorted in ascending order."""
  result = angles
  for i in range(1, len(angles)):
    if result[i] < result[i-1]: result[i] += 360

  assert(result == sorted(result))
  return result

def inverse_lagrange(x, y, ya):
  """Given two lists x and y, find the value of x = xa when y = ya, i.e., f(xa) = ya"""
  assert(len(x) == len(y))
  total = 0
  for i in range(len(x)):
    numer = 1
    denom = 1
    for j in range(len(x)):
      if j != i:
        numer *= (ya - y[j])
        denom *= (y[i] - y[j])

    total += numer * x[i] / denom

  return total

# Julian Day number as on (year, month, day) at 00:00 UTC
gregorian_to_jd = lambda date: swe.julday(date.year, date.month, date.day, 0.0)
jd_to_gregorian = lambda jd: swe.revjul(jd, swe.GREG_CAL)   # returns (y, m, d, h, min, s)

def solar_longitude(jd):
  """Solar longitude at given instant (julian day) jd"""
  data = swe.calc_ut(jd, swe.SUN, flag = swe.FLG_SWIEPH)
  return data[0]   # in degrees

def lunar_longitude(jd):
  """Lunar longitude at given instant (julian day) jd"""
  data = swe.calc_ut(jd, swe.MOON, flag = swe.FLG_SWIEPH)
  return data[0]   # in degrees

def lunar_latitude(jd):
  """Lunar latitude at given instant (julian day) jd"""
  data = swe.calc_ut(jd, swe.MOON, flag = swe.FLG_SWIEPH)
  return data[1]   # in degrees

def sunrise(jd, place):
  """Sunrise when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=swe.BIT_DISC_CENTER + swe.CALC_RISE)
  rise = result[1][0]  # julian-day number
  # Convert to local time
  return [rise + tz/24., to_dms((rise - jd) * 24 + tz)]

def sunset(jd, place):
  """Sunset when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=swe.BIT_DISC_CENTER + swe.CALC_SET)
  setting = result[1][0]  # julian-day number
  # Convert to local time
  return [setting + tz/24., to_dms((setting - jd) * 24 + tz)]

def moonrise(jd, place):
  """Moonrise when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.MOON, lon, lat, rsmi=swe.BIT_DISC_CENTER + swe.CALC_RISE)
  rise = result[1][0]  # julian-day number
  # Convert to local time
  return to_dms((rise - jd) * 24 + tz)

def moonset(jd, place):
  """Moonset when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.MOON, lon, lat, rsmi=swe.BIT_DISC_CENTER + swe.CALC_SET)
  setting = result[1][0]  # julian-day number
  # Convert to local time
  return to_dms((setting - jd) * 24 + tz)

# Tithi doesn't depend on Ayanamsa
def tithi(jd, place):
  """Tithi at sunrise for given date and place. Also returns tithi's end time."""
  tz = place.timezone
  # 1. Find time of sunrise
  rise = sunrise(jd, place)[0] - tz / 24

  # 2. Find tithi at this JDN
  moon_phase = lunar_phase(rise)
  today = ceil(moon_phase / 12)
  degrees_left = today * 12 - moon_phase

  # 3. Compute longitudinal differences at intervals of 0.25 days from sunrise
  offsets = [0.25, 0.5, 0.75, 1.0]
  lunar_long_diff = [ (lunar_longitude(rise + t)[0] - lunar_longitude(rise)[0]) % 360 for t in offsets ]
  solar_long_diff = [ (solar_longitude(rise + t)[0] - solar_longitude(rise)[0]) % 360 for t in offsets ]
  relative_motion = [ moon - sun for (moon, sun) in zip(lunar_long_diff, solar_long_diff) ]

  # 4. Find end time by 4-point inverse Lagrange interpolation
  y = relative_motion
  x = offsets
  # compute fraction of day (after sunrise) needed to traverse 'degrees_left'
  approx_end = inverse_lagrange(x, y, degrees_left)
  ends = (rise + approx_end -jd) * 24 + tz
  answer = [int(today % 31), to_dms(ends)]

  # 5. Check for skipped tithi
  moon_phase_tmrw = lunar_phase(rise + 1)
  tomorrow = ceil(moon_phase_tmrw / 12)
  isSkipped = (tomorrow - today) % 30 > 1
  if isSkipped:
    # interpolate again with same (x,y)
    leap_tithi = today + 1
    degrees_left = leap_tithi * 12 - moon_phase
    approx_end = inverse_lagrange(x, y, degrees_left)
    ends = (rise + approx_end -jd) * 24 + place.timezone
    answer += [int(leap_tithi % 30), to_dms(ends)]

  return answer


def nakshatra(jd, place):
  """Current nakshatra as of julian day (jd)
     1 = Asvini, 2 = Bharani, ..., 27 = Revati
  """
  swe.set_sid_mode(swe.SIDM_LAHIRI)
  # 1. Find time of sunrise
  lat, lon, tz = place
  rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

  # Swiss Ephemeris always gives Sayana. So subtract ayanamsa to get Nirayana
  offsets = [0.0, 0.25, 0.5, 0.75, 1.0]
  longitudes = [ (lunar_longitude(rise + t)[0] - swe.get_ayanamsa_ut(rise)) % 360 for t in offsets]

  # 2. Today's nakshatra is when offset = 0
  # There are 27 Nakshatras spanning 360 degrees
  nak = ceil(longitudes[0] * 27 / 360)

  # 3. Find end time by 5-point inverse Lagrange interpolation
  y = unwrap_angles(longitudes)
  x = offsets
  approx_end = inverse_lagrange(x, y, nak * 360 / 27)
  ends = (rise - jd + approx_end) * 24 + tz
  answer = [int(nak), to_dms(ends)]

  # 4. Check for skipped nakshatra
  nak_tmrw = ceil(longitudes[-1] * 27 / 360)
  isSkipped = (nak_tmrw - nak) % 27 > 1
  if isSkipped:
    leap_nak = nak + 1
    approx_end = inverse_lagrange(offsets, longitudes, leap_nak * 360 / 27)
    ends = (rise - jd + approx_end) * 24 + tz
    answer += [int(leap_nak % 27), to_dms(ends)]

  return answer


def yoga(jd, place):
  """Yoga at given jd and place.
     1 = Vishkambha, 2 = Priti, ..., 27 = Vaidhrti
  """
  swe.set_sid_mode(swe.SIDM_LAHIRI)
  # 1. Find time of sunrise
  lat, lon, tz = place
  rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

  # 2. Find the Nirayana longitudes and add them
  lunar_long = (lunar_longitude(rise)[0] - swe.get_ayanamsa_ut(rise)) % 360
  solar_long = (solar_longitude(rise)[0] - swe.get_ayanamsa_ut(rise)) % 360
  total = (lunar_long + solar_long) % 360
  # There are 27 Yogas spanning 360 degrees
  yog = ceil(total * 27 / 360)

  # 3. Find how many longitudes is there left to be swept
  degrees_left = yog * (360 / 27) - total

  # 3. Compute longitudinal sums at intervals of 0.25 days from sunrise
  offsets = [0.25, 0.5, 0.75, 1.0]
  lunar_long_diff = [ (lunar_longitude(rise + t)[0] - lunar_longitude(rise)[0]) % 360 for t in offsets ]
  solar_long_diff = [ (solar_longitude(rise + t)[0] - solar_longitude(rise)[0]) % 360 for t in offsets ]
  total_motion = [ moon + sun for (moon, sun) in zip(lunar_long_diff, solar_long_diff) ]

  # 4. Find end time by 4-point inverse Lagrange interpolation
  y = total_motion
  x = offsets
  # compute fraction of day (after sunrise) needed to traverse 'degrees_left'
  approx_end = inverse_lagrange(x, y, degrees_left)
  ends = (rise + approx_end - jd) * 24 + tz
  answer = [int(yog), to_dms(ends)]

  # 5. Check for skipped yoga
  lunar_long_tmrw = (lunar_longitude(rise + 1)[0] - swe.get_ayanamsa_ut(rise + 1)) % 360
  solar_long_tmrw = (solar_longitude(rise + 1)[0] - swe.get_ayanamsa_ut(rise + 1)) % 360
  total_tmrw = (lunar_long_tmrw + solar_long_tmrw) % 360
  tomorrow = ceil(total_tmrw * 27 / 360)
  isSkipped = (tomorrow - yog) % 27 > 1
  if isSkipped:
    # interpolate again with same (x,y)
    leap_yog = yog + 1
    degrees_left = leap_yog * (360 / 27) - total
    approx_end = inverse_lagrange(x, y, degrees_left)
    ends = (rise + approx_end - jd) * 24 + tz
    answer += [int(leap_yog %27), to_dms(ends)]

  return answer


def karana(jd, place):
  """Returns the karana and their ending times. (from 1 to 60)"""
  # 1. Find time of sunrise
  rise = sunrise(jd, place)[0]

  # 2. Find karana at this JDN
  solar_long = solar_longitude(rise)[0]
  lunar_long = lunar_longitude(rise)[0]
  moon_phase = (lunar_long - solar_long) % 360
  today = ceil(moon_phase / 6)
  degrees_left = today * 6 - moon_phase

  return [int(today)]

def vaara(jd):
  """Weekday for given Julian day. 0 = Sunday, 1 = Monday,..., 6 = Saturday"""
  return int(ceil(jd + 1) % 7)

def masa(jd, place):
  """Returns lunar month and if it is adhika or not.
     1 = Chaitra, 2 = Vaisakha, ..., 12 = Phalguna"""
  ti = tithi(jd, place)[0]
  critical = sunrise(jd, place)[0]  # - tz/24 ?
  last_new_moon = new_moon(critical, ti, -1)
  next_new_moon = new_moon(critical, ti, +1)
  this_solar_month = raasi(last_new_moon)
  next_solar_month = raasi(next_new_moon)
  is_leap_month = (this_solar_month == next_solar_month)
  maasa = this_solar_month + 1
  if maasa > 12: maasa = (maasa % 12)
  return [int(maasa), is_leap_month]

# epoch-midnight to given midnight
# Days elapsed since beginning of Kali Yuga
ahargana = lambda jd: jd - 588465.5

def elapsed_year(jd, maasa_num):
  sidereal_year = 365.25636
  ahar = ahargana(jd)  # or (jd + sunrise(jd, place)[0])
  kali = int((ahar + (4 - maasa_num) * 30) / sidereal_year)
  saka = kali - 3179
  vikrama = saka + 135
  return kali, saka

# New moon day: sun and moon have same longitude (0 degrees = 360 degrees difference)
# Full moon day: sun and moon are 180 deg apart
def new_moon(jd, tithi_, opt = -1):
  """Returns JDN, where
     opt = -1:  JDN < jd such that lunar_phase(JDN) = 360 degrees
     opt = +1:  JDN >= jd such that lunar_phase(JDN) = 360 degrees
  """
  if opt == -1:  start = jd - tithi_         # previous new moon
  if opt == +1:  start = jd + (30 - tithi_)  # next new moon
  # Search within a span of (start +- 2) days
  x = [ -2 + offset/4 for offset in range(17) ]
  y = [lunar_phase(start + i) for i in x]
  y = unwrap_angles(y)
  y0 = inverse_lagrange(x, y, 360)
  return start + y0

# Full moon day: sun and moon are 180 deg apart
def full_moon(jd, tithi_, opt = -1):
  """Returns JDN, where
     opt = -1:  JDN < jd such that lunar_phase(JDN) = 360 degrees
     opt = +1:  JDN >= jd such that lunar_phase(JDN) = 360 degrees
  """
  if opt == -1:  start = jd - tithi_         # previous new moon
  if opt == +1:  start = jd + (30 - tithi_)  # next new moon
  # Search within a span of (start +- 2) days
  x = [ -2 + offset/4 for offset in range(17) ]
  y = [lunar_phase(start + i) for i in x]
  y = unwrap_angles(y)
  y0 = inverse_lagrange(x, y, 180)
  return start + y0

def raasi(jd):
  """Zodiac of given jd. 1 = Mesha, ... 12 = Meena"""
  swe.set_sid_mode(swe.SIDM_LAHIRI)
  s = solar_longitude(jd)[0]
  solar_nirayana = (solar_longitude(jd)[0] - swe.get_ayanamsa_ut(jd)) % 360
  # 12 rasis occupy 360 degrees, so each one is 30 degrees
  return ceil(solar_nirayana / 30.)

def lunar_phase(jd):
  solar_long = solar_longitude(jd)
  lunar_long = lunar_longitude(jd)
  #moon_phase = (lunar_long, solar_long) % 360
  #moon_phase = np.subtract((lunar_long, solar_long)) % 360
  #moon_phase = tuple(map(sub, lunar_long, solar_long))
  moon_phase = lunar_long[0] - solar_long[0]
  moon_phase = moon_phase % 360
  return moon_phase

def samvatsara(jd, maasa_num):
  kali = elapsed_year(jd, maasa_num)[0]
  # Change 14 to 0 for North Indian tradition
  # See the function "get_Jovian_Year_name_south" in pancanga.pl
  if kali >= 4009:    kali = (kali - 14) % 60
  samvat = (kali + 27 + int((kali * 211 - 108) / 18000)) % 60
  return samvat

def ritu(masa_num):
  """0 = Vasanta,...,5 = Shishira"""
  return (masa_num - 1) // 2

def day_duration(jd, place):
  srise = sunrise(jd, place)[0]  # julian day num
  sset = sunset(jd, place)[0]    # julian day num
  diff = (sset - srise) * 24     # In hours
  return [diff, to_dms(diff)]

# Global functions
# Converts list [12, [23, 45, 50]] to lookup[12] and 23:45:50
def format_name_hms(nhms, lookup):
    name_txt = lookup[str(nhms[0])]
    time_txt = format_time(nhms[1])
    if len(nhms) == 4:
        name_txt += "\n" + lookup[str(nhms[2])]
        time_txt += "\n" + format_time(nhms[3])

    return  name_txt, time_txt

def compute_timezone_offset(year, month, day, tzone):
    timezone = tzone
    dt = datetime(year, month, day)
    # offset from UTC (in hours). Needed especially for DST countries
    tz_offset = timezone.utcoffset(dt, is_dst = True).total_seconds() / 3600.
    return tz_offset

def compute_detailed_info_for_given_dates(location, date, extra_option, debug):
    if debug:
       print("Given date (%s) extra Option (%s):" %(date, extra_option))
    if extra_option == 'None':
       date_info = compute_detailed_info_for_a_given_day(location, date, debug)
       #print (date_info)
       #x = json.dumps(date_info)
       #print(x)
       return date_info
    if extra_option == 'm':
       date_info = compute_detailed_info_for_a_given_month(location, date, debug)
       return date_info
    if extra_option == 'y':
       date_info = compute_detailed_info_for_a_given_year(location, date, debug)

def compute_detailed_info_for_a_given_year(location, date, debug):

    if debug:
        print("Given date (%s)" %(date))
    (dd,mm,yyyy) = date.split('-')
    i_dd=int(dd)
    i_mm=int(mm)
    i_yy=int(yyyy)
    
    jd = gregorian_to_jd(Date(i_yy, i_mm, i_dd))
    
    tzname = location['timezone']
    tzoff=timezone(tzname)
    tzoffset = compute_timezone_offset(i_yy, i_mm, i_dd, tzoff)
    place = Place( location['latitude'], location['longitude'], tzoffset)
     
    maasa = 12
    i = 0
    cur_new_moon = jd
    last_new_moon_date = jd_to_gregorian(jd)
     
    while maasa != 1:
      tit = tithi(jd, place)[0]
      critical = sunrise(jd, place)[0]
      last_new_moon = new_moon(critical, tit, -1)
      last_new_moon_date = jd_to_gregorian(last_new_moon)
      if debug:
        print("{last_new_moon: %s  %s}"  %(format_date(last_new_moon_date), jd))
      if last_new_moon == cur_new_moon:
        jd = jd - 1 # reduce one day and go to previous telugu month and test
      else:
        jd = last_new_moon
      cur_new_moon = last_new_moon
      last_new_moon_date = jd_to_gregorian(last_new_moon)
      this_solar_month = raasi(last_new_moon)
      maasa = this_solar_month + 1
      if maasa > 12: maasa = (maasa % 12)
      if debug:
        print("{last_new_moon month: %s  %s %d}"  %(format_date(last_new_moon_date), jd, maasa))
    
    yugadi_jd   = jd_to_gregorian(last_new_moon+1)
    if debug:
        print("Yugadi in Gregorain Date is: %s" % (format_date(yugadi_jd)))

    print("Yugadi in Gregorain Date is: %s" % (format_date(yugadi_jd)))
    rVal = {}
    i = 1
    month_start_jd = yugadi_jd
    while i > 0 and i < 13:
        yugadi_start_date = format_date(month_start_jd)
        month_info =  compute_detailed_info_for_a_given_month(location, yugadi_start_date, debug)
        rVal[i] = month_info;
        print (month_info)
        cur_month_end_date = month_info['monthInfo']['end_date']
        if debug:
            print("This month_last_date %s" %(cur_month_end_date))
        (dd,mm,yyyy) = cur_month_end_date.split('-')
        i_dd=int(dd)
        i_mm=int(mm)
        i_yy=int(yyyy)
        jd = gregorian_to_jd(Date(i_yy, i_mm, i_dd))
        month_start_jd =  jd_to_gregorian(jd + 1)
        i =  i + 1
      
    sys.exit(2)


def compute_next_gegorian_date_of_give_hindu_data(location, date, tithi_given, masam_given, debug):
    if debug:
        #print("Given date (%s)" %(date))
        print("Tithi and Masam are given, now calculate Greogorian Dates of current year")

    (dd,mm,yyyy) = date.split('-')
    i_dd=int(dd)
    i_mm=int(mm)
    i_yy=int(yyyy)
    
    jd = gregorian_to_jd(Date(i_yy, i_mm, i_dd))
    
    tzname = location['timezone']
    tzoff=timezone(tzname)
    tzoffset = compute_timezone_offset(i_yy, i_mm, i_dd, tzoff)
    place = Place( location['latitude'], location['longitude'], tzoffset)

    ti = tithi(jd, place)
    masam = masa(jd, place)
    nak = nakshatra(jd, place)

    i = 0
    cur_new_moon = jd
    next_new_moon_date = jd_to_gregorian(jd)
     
    while masam_given != masam:
      tit = tithi(jd, place)[0]
      critical = sunrise(jd, place)[0]
      next_new_moon = new_moon(critical, tit, +1)
      next_new_moon_date = jd_to_gregorian(next_new_moon)
      if debug:
        print("{next_new_moon: %s  %s}"  %(format_date(next_new_moon_date), jd))
      if next_new_moon == cur_new_moon:
        jd = jd + 1 # increase one day and go to next telugu month and test
      else:
        jd = next_new_moon
      cur_new_moon = next_new_moon
      next_new_moon_date = jd_to_gregorian(next_new_moon)
      this_solar_month = raasi(next_new_moon)
      masam = this_solar_month + 1
      if masam > 12: masam = (masam % 12)
      if debug:
        print("{next_new_moon month: %s  %s %d %d %d}"  %(format_date(next_new_moon_date), jd, masam, masam_given, tithi_given))

    cur_date = jd_to_gregorian(jd)
    tit = tithi(jd, place)[0]
    # it is observed that if gievn tithi is amavasya, then below logic is priting last month's amavasa instead of cur month
    if tit == 30: tit = 1
    while tithi_given != tit:
      jd = jd + 1
      tit = tithi(jd, place)[0]
      cur_date = jd_to_gregorian(jd)
      if debug:
        print("{cur_tithi: %s  %s %d %d %d %d}"  %(format_date(cur_date), jd, masam, masam_given, tithi_given, tit))
      if tit > 30: tit = (tit % 30)

    # open all names which are needed so that can display in str
    fp = open("sanskrit_en_names.json")
    sktnames = json.load(fp)
    fp.close()

    tithis = sktnames["tithis"]
    nakshatras = sktnames["nakshatras"]
    masas = sktnames["masas"]
    vaaras = sktnames["varas"]

    ti = tithi(jd, place)
    nak = nakshatra(jd, place)
    mas = masa(jd, place)
    vara = vaara(jd)
    date_info = dict()

    if debug:
        print("Given Titthi %s and Masam %s" % ( tithis[str(tithi_given)], masas[str(masam_given)]))

    date_info['gregorian_date']=format_date(cur_date)

    if debug == 1:
      print("{Varam:  %s}" % vaaras[str(vara)])
    date_info['varam']=vaaras[str(vara)]

    name, hms = format_name_hms(ti, tithis)
    if debug == 1:
      print("{Thiti: %s %s}" % (name,hms))
    date_info['tithi']=name
    date_info['tithi_time']=hms

    name, hms = format_name_hms(nak, nakshatras)
    if debug == 1:
      print("{Nakshatra: %s %s}" % (name, hms))
    date_info['nakshatra']=name
    date_info['nakshatra_time']=hms

    # Next update the complex ones
    month_name = masas[str(mas[0])]
    month_name = month_name + " masa"
    if debug == 1:
      print("{Masam: %s}" % (month_name))
    date_info['masam']=month_name

    print(date_info)
    sys.exit(2)


def compute_detailed_info_for_a_given_month(location, date, debug):
    rVal = {}
    if debug:
        print("Given date (%s)" %(date))
    (dd,mm,yyyy) = date.split('-')
    i_dd=int(dd)
    i_mm=int(mm)
    i_yy=int(yyyy)

    jd = gregorian_to_jd(Date(i_yy, i_mm, i_dd))

    tzname = location['timezone']
    tzoff=timezone(tzname)
    tzoffset = compute_timezone_offset(i_yy, i_mm, i_dd, tzoff)
    place = Place( location['latitude'], location['longitude'], tzoffset)

    tit = tithi(jd, place)[0]
    critical = sunrise(jd, place)[0]  # - tz/24 ?
    last_new_moon = new_moon(critical, tit, -1)
    next_new_moon = new_moon(critical, tit, +1)
    last_new_moon_date=jd_to_gregorian(last_new_moon)
    next_new_moon_date=jd_to_gregorian(next_new_moon)

    #print("{last_new_moon: %s}"  %(format_date(last_new_moon_date)))
    #print("{next_new_moon: %s}"  %(format_date(next_new_moon_date)))
    date_format="%d-%m-%Y"
   
    month_start = last_new_moon + 1
    last_new_moon_date=jd_to_gregorian(month_start)
    i_start_day=last_new_moon_date[2]
    i_start_month=last_new_moon_date[1]
    i_start_year=last_new_moon_date[0]
 
    total_month = []
    sukla_list = []
    krishna_list = []
    ti = 'None'
    i = 0
    start_krishna_paksha = 0
    month_info = dict()

    start_date=format_date(Date(i_start_year,i_start_month,i_start_day))
    month_info['start_date']=start_date
    month_info['month_name']='None'
    cur_month = 'None'
    #while ti != 'Amavasya' and cur_month == month_info['month_name']:
    #TBD a possible bug is when last tithi is not amavasa due to shorter durations of thitis ... need a fix
    while ti != 'Amavasya' and i < 32:
         start_date=format_date(Date(i_start_year,i_start_month,i_start_day))
         try:
             datetime.strptime(start_date,date_format)
             #print("Given a good day %s" %(start_date))
             date_info = compute_detailed_info_for_a_given_day(location, start_date, 0)

             if date_info['tithi'] == 'Purnima':
                 month_info['purnami']=start_date
                 month_info['month_name']=date_info['masam']
             if date_info['tithi'] == 'Amavasya':
                 month_info['amavasya']=start_date
             if date_info['tithi'] == 'Krishna paksa prathama':
                 start_krishna_paksha=1

             #cur_month = date_info['masam']

             #Switch between Krishna and Sukla Pakshas
             if start_krishna_paksha == 1: 
                krishna_list.append(date_info)
             else:
                sukla_list.append(date_info)

             i_start_day=i_start_day + 1
             #cross check if next day is also a Amavasya day or not!!
             if date_info['tithi'] == 'Amavasya':
                start_date=format_date(Date(i_start_year,i_start_month,i_start_day))
                try:
                   datetime.strptime(start_date,date_format)
                   #print("Given a good day %s" %(start_date))
                   date_info = compute_detailed_info_for_a_given_day(location, start_date, 0)
                   if date_info['tithi'] == 'Amavasya':
                      krishna_list.append(date_info)
                   else:
                       date_info['tithi'] = 'Amavasya' # assign amavasya so that code will break
                except:
                  #do nothing
                  i_start_day=i_start_day - 1
                  start_date=format_date(Date(i_start_year,i_start_month,i_start_day))
         except:
             #print_err_and_exit(parser, "option (-d) requires proper date in DD-MM-YYYY format")
             #print("Given a bad day %s, change the month and check" %(start_date))
             i_start_day=1
             if i_start_month >= 12:
                i_start_month=1;
                i_start_year=last_new_moon_date[0]+1
             else:
                i_start_month=last_new_moon_date[1]+1

         # update the thithi so that code can exit smoothly
         try:
            ti=date_info['tithi']
         except:
            ti='Amavasya'

         #safe side iterate through only 33 times not beyond that
         i = i + 1

    month_info['end_date']=start_date

    rVal['monthInfo'] = month_info;
    
    if debug:
        print("Month Details:")
    #total_month.append(month_info)
    #print(month_info) 
    
    if debug:
        print("Sukla Paksha Thithis:")
    rVal['suklaPaksham'] = sukla_list
    #print(sukla_list) 
    #for p in sukla_list:
    #    #print (p)
    #    total_month.append(p)

    if debug:
        print("Krishna Paksha Thithis:")
    rVal['krishnaPaksham'] = krishna_list
    #print(krishna_list) 
    #for p in krishna_list:
    #    total_month.append(p)
    #    #print (p)

    #x = json.dumps(total_month)
    return rVal

def compute_detailed_info_for_a_given_day(location, date, debug):
    if debug == 1:
      print("Given date (%s)" %(date))

    (dd,mm,yyyy) = date.split('-')
    i_dd=int(dd)
    i_mm=int(mm)
    i_yy=int(yyyy)

    jd = gregorian_to_jd(Date(i_yy, i_mm, i_dd))
    # open all names which are needed so that can display in str
    fp = open("sanskrit_en_names.json")
    sktnames = json.load(fp)
    fp.close()

    tithis = sktnames["tithis"]
    nakshatras = sktnames["nakshatras"]
    vaaras = sktnames["varas"]
    yogas = sktnames["yogas"]
    karanas = sktnames["karanas"]
    masas = sktnames["masas"]
    samvats = sktnames["samvats"]
    ritus = sktnames["ritus"]  

    tzname = location['timezone']
    tzoff=timezone(tzname)
    tzoffset = compute_timezone_offset(i_yy, i_mm, i_dd, tzoff)
    #Tirupati {'latitude': 13.65, 'timezone': 'Asia/Kolkata', 'longitude': 79.41667}
    #place = Place( 13.65, 79.41667, +5.5) 
    place = Place( location['latitude'], location['longitude'], tzoffset) 
    ti = tithi(jd, place)
    nak = nakshatra(jd, place)
    yog = yoga(jd, place)
    mas = masa(jd, place)
    rtu = ritu(mas[0])
    kar = karana(jd, place)
    vara = vaara(jd)
    srise = sunrise(jd, place)[1]
    sset = sunset(jd, place)[1]
    kday = ahargana(jd)
    kyear, sakayr = elapsed_year(jd, mas[0])
    samvat = samvatsara(jd, mas[0])
    day_dur = day_duration(jd, place)[1]
    mrise = moonrise(jd, place)
    mset = moonset(jd, place)

    date_info = dict()

    date_info['gregorian_date']=date

    #if debug == 1:
    #  print("{\n{Karanam: %s}" %str(kar[0]))
    #date_info['karanam']=str(kar[0])

    if debug == 1:
      print("{Varam:  %s}" % vaaras[str(vara)])
    date_info['varam']=vaaras[str(vara)]

    if debug == 1:
      print("{SunRise: %s}" % format_time(srise))
    date_info['sunrise']=format_time(srise)
    if debug == 1:
      print("{SunSet: %s}" % format_time(sset))
    date_info['sunset']=format_time(srise)

    if debug == 1:
      print("{MoonRise: %s}" % format_time(mrise))
    date_info['mrise']=format_time(mrise)

    if debug == 1:
      print("{MoonSet: %s}" % format_time(mset))
    date_info['mset']=format_time(mrise)

    name, hms = format_name_hms(ti, tithis)
    if debug == 1:
      print("{Thiti: %s %s}" % (name,hms))
    date_info['tithi']=name
    date_info['tithi_time']=hms

    name, hms = format_name_hms(nak, nakshatras)
    if debug == 1:
      print("{Nakshatra: %s %s}" % (name, hms))
    date_info['nakshatra']=name
    date_info['nakshatra_time']=hms
    if debug == 1:
      print("{Telugu Samvasaram: %s samvatsara}" % (samvats[str(samvat)]))
    date_info['samvasaram']=samvats[str(samvat)]
    if debug == 1:
      print("{Day Duration: %s}" % format_time(day_dur))
    date_info['day_duration']=format_time(day_dur)

    # Next update the complex ones
    month_name = masas[str(mas[0])]
    is_leap = mas[1]
    if is_leap:  month_name = "Adhika " + month_name.lower()
    month_name = month_name + " masa"
    if debug == 1:
      print("{Masam: %s}" % (month_name))
    date_info['masam']=month_name
    if debug == 1:
      print("{Ruthuvu: %s ṛtu}" % (ritus[str(rtu)]))
    date_info['ruthuvu']=ritus[str(rtu)]

    ##Use it when needed, as of now this data is not used
    #name, hms = format_name_hms(yog, yogas)
    #if debug == 1:
    #  print("{Yuga: %s}" % (name))
    #date_info['yuga']=name
    #if debug == 1:
    #  print("{GataKali: %d}" % (kyear))
    #date_info['gataKali']=kyear
    #if debug == 1:
    #  print("{KaliDay: %d}" % (kday))
    #date_info['kaliday']=kday
    #if debug == 1:
    #  print("{Skayra: %s}" % (sakayr))
    #date_info['skayra']=sakayr
    #if debug == 1:
    #  print("{Śālivāhana śaka: %d}\n}" % (sakayr))
    #date_info['salivahana_saka']=sakayr

    return date_info

def list_location(locationName, verbose):
    # open all cities json files and parse all cities data
    fp = open("cities.json")
    cities = json.load(fp)
    all_cities = cities.keys()
    fp.close()
    #print(cities)
    location='None'
    if locationName != 'None':
        try:
          location=cities[str(locationName)]
        except:
          print("Couldnt find given location (%s) information." % (locationName))
        if location != 'None':
            if verbose:
              print("location exists in DB: Location:%s Details:%s" %(locationName, location))
            else:
              print("location exists in DB: %s" %(locationName))
    if location == 'None':
       print("Printing all locations information:")
       if verbose:
         for i in cities.items():
           print (i)
       else:
         for i in all_cities:
           print (i)
    #print(all_cities)

def find_given_location_from_static_db(locationName):
    # open all cities json files and parse all cities data
    fp = open("cities.json")
    cities = json.load(fp)
    all_cities = cities.keys()
    fp.close()
    try:
       location=cities[str(locationName)]
    except:
       print("Couldnt find given location (%s) information." % (locationName))
       print_err_and_exit(parser, SUB_C_L_USAGE_STR)
    return location

def print_err_and_exit(parser, errMsg):
    parser.error(errMsg)
    print(MAIN_USAGE_STR)
    sys.exit(2)

if __name__ == "__main__":

  # parse all input options
  parser = optparse.OptionParser(usage="usage: %prog -C -l location -d DD-MM-YYYY [-e [m|y]] [-v] \n"
                                       "usage: %prog -C -x longitude -y latitude -t timezone -d DD-MM-YYYY [-e [m|y]] [-v] \n"
                                       "usage: %prog -C -l location -i [1-30] -m [1-13] [-v] \n"
                                       "usage: %prog -C -x longitude -y latitude -t timezone -i tithi -m masam [-v] \n"
                                       "usage: %prog -L [Location_Name] [-v] \n",
                                       version = "%prog 1.0")

  parser.add_option("-L", "--list-all-locations", action="store_true", dest="list_all_locations",help="Lists all available locations or Specific location defined by name")
  parser.add_option("-C", "--calculate-calander", action="store_true", dest="calculate_calander",help="Displays calander for given date")
  parser.add_option("-v", "--verbose", action="store_true", dest="verbose",help="All functions and commands outputs in verbose mode, used for debugging")
  parser.add_option("-x", "--latitude", action="store_true", dest="latitude_given",help="suboption of -C, should be used along with -y, -t, provide a proper latitude of needed location")
  parser.add_option("-y", "--longitude", action="store_true", dest="longitude_given",help="suboption of -C, should be used along with -x, -t,provide a proper longitude of needed location")
  parser.add_option("-t", "--time_zone", action="store_true", dest="timezone_given",help="suboption of -C, should be used along with -x, -y,provide proper timezone of needed location")
  parser.add_option("-l", "--location", action="store_true", dest="location_given",help="suboption of -C, provide correct location extracted using -L command")
  parser.add_option("-d", "--date", action="store_true", dest="date_given",help="suboption of -C, provide a proper date in DD-MM-YYYY format")
  parser.add_option("-e", "--extra_info", action="store_true", dest="extra_given",help="suboption of -C and -d, provide whether u need a months calander[m] or years calander[y]")
  parser.add_option("-i", "--tithi_info", action="store_true", dest="tithi_given",help="suboption of -C and should be used with -l and -m, provide the thiti between and 1 and 30, where 1 is sukla paksha ekadasi and 30 is amavasya")
  parser.add_option("-m", "--masam_info", action="store_true", dest="masam_given",help="suboption of -C and should be used with -l and -i, provide the masam between 1 and 12, where 1 is Caitra and 12 is Phalguna")

  (options, args) = parser.parse_args()

  #enablde/disable debug using verbose, default disabled
  verbose = 0
  if options.verbose:
    verbose = 1

  #List all locations from sattic database
  if options.list_all_locations:
    locationName='None'
    if args:
        locationName=args[0]
    list_location(locationName, verbose)
    sys.exit(2)
 
  location = dict()

  #calculate detailed panchangam for a given greogorian date and location
  if options.calculate_calander:
    extra_option='None'
    #no argumemts given, throw error
    if not args:
        print_err_and_exit(parser, MAIN_USAGE_STR)
    else:
        #read the location information, which is mandatory parameter for calculating detailed info 
        #if location (-l) is given then use it
        if options.location_given:
            locationName=args[0]
            location = find_given_location_from_static_db(locationName)
            if verbose:
                print("Location Details: %s %s" %(locationName, location))
        #if location ( in longitude, latitude, timzeone ) is given then use it
        elif options.longitude_given and options.latitude_given and options.timezone_given :
            location['latitude'] = float(args[0])
            location['longitude'] = float(args[1])
            location['timezone'] = args[2]
            if verbose:
                print("Location Details: %s" %(location))
        #if not then it is an error 
        else :
            print("Location not specified, please provide correct location.")
            print_err_and_exit(parser, MAIN_OPT_C_USAGE_STR)

        #read the date which is mandatory parameter for calculating detailed info 
        if options.date_given:
            if options.longitude_given and options.latitude_given and options.timezone_given :
                date=args[3]
            else:
                date=args[1]
            date_format="%d-%m-%Y"

            try:
                datetime.strptime(date,date_format)
            except:
                print_err_and_exit(parser, SUB_C_D_USAGE_STR)
        
       #read the extra optional paramter (-e), which will tell whether to display monthy or yearly info
        if options.extra_given:
            if not options.date_given:
                print_err_and_exit(parser, "Date (-d) is mandatory parameter for -e option" + "\n" + MAIN_USAGE_STR)
            if options.date_given and options.longitude_given and options.latitude_given and options.timezone_given :
                try :
                    extra_option=args[4]
                except:
                    print_err_and_exit(parser, SUB_C_E_USAGE_STR + "\n" + MAIN_USAGE_STR)
            elif options.date_given and options.location_given:
                try :
                    extra_option=args[2]
                except:
                    print_err_and_exit(parser, SUB_C_E_USAGE_STR + "\n" + MAIN_USAGE_STR)
            else:
                print_err_and_exit(parser, SUB_C_E_USAGE_STR + "\n" + MAIN_USAGE_STR)

            #curently supporting monthly or yearly info only
            if extra_option != 'm' and extra_option != 'y':
                print("Invalid input value (%s) for -e option, provide either m or y." %(extra_option))
                print_err_and_exit(parser, MAIN_USAGE_STR)

        #read the tithi and masam given by user and start calculating gregorian date 
        if options.tithi_given and options.masam_given:
            if options.date_given and options.longitude_given and options.latitude_given and options.timezone_given :
                try :
                    given_tithi=int(args[4])
                    given_masam=int(args[5])
                except:
                    print_err_and_exit(parser, SUB_C_IM_USAGE_STR + "\n" + MAIN_USAGE_STR)
            elif options.date_given and options.location_given:
                try :
                    given_tithi=int(args[2])
                    given_masam=int(args[3])
                except:
                    print_err_and_exit(parser, SUB_C_IM_USAGE_STR + "\n" + MAIN_USAGE_STR)
            else:
                print_err_and_exit(parser, SUB_C_IM_USAGE_STR + "\n" + MAIN_USAGE_STR)

            if given_tithi < 1 or given_tithi > 30:
                print("Invalid input value (%s) for -i option, provide in range 1-30." %(given_tithi))
                print_err_and_exit(parser, SUB_C_IM_USAGE_STR + "\n" + MAIN_USAGE_STR)
            if given_masam < 1 or given_masam > 12:
                print("Invalid input value (%s) for -m option, provide in range 1-12." %(given_masam))
                print_err_and_exit(parser, SUB_C_IM_USAGE_STR + "\n" + MAIN_USAGE_STR)

            compute_next_gegorian_date_of_give_hindu_data(location, date, given_tithi, given_masam, verbose)
            sys.exit(2)

        computedDict = compute_detailed_info_for_given_dates(location, date, extra_option, verbose)
        print(json.dumps(computedDict))
        sys.exit(2)

  print("Usage:\n%s" % (MAIN_USAGE_STR))
  sys.exit(2)
