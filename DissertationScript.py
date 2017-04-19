from subprocess import call
import os
import pandas as pd
from pandas import DataFrame
import string
import re
from urllib.request import urlopen
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.select import Select
from selenium.webdriver.support.ui import WebDriverWait
from selenium.common import exceptions
from selenium.webdriver.common.action_chains import ActionChains
import time
import nltk
from collections import defaultdict, Counter
from nltk.corpus import stopwords
from nltk import FreqDist, ConditionalFreqDist
import datetime
#import yaml
from xml.etree import ElementTree
from difflib import SequenceMatcher
import json
import difflib

#Get username and PW from text file
with open("../CSpanUserNamePW.txt","r") as f:
    f = f.read()
    username = f.split("\t")[0]
    pw = f.split("\t")[1]

#This scrapes the Congressional Record transcripts from each committee
def gpo_scrape():
    li=[]
    for num in range(95,115):
        for agen in ["HOUSE","JOINT","SENATE"]:
            url = "http://www.gpo.gov/fdsys/browse/collection.action?collectionCode=CHRG&browsePath="+str(num)+"%2F"+agen+"&isCollapsed=false&leafLevelBrowse=false&ycord=0"
            url = urlopen(url).read().decode()
            reg = re.compile(str(num)+'/'+agen+'/'+'(.*?)3')
            reg = re.findall(reg,url)
            for a in reg:
                temp = re.sub(' ','+',a)
                path = str(num)+"%2F"+str(agen)+"%2F"+str(temp)
                url2 = "http://www.gpo.gov/fdsys/browse/collection.action?collectionCode=CHRG&browsePath="+str(path)+"&isCollapsed=false&leafLevelBrowse=false&isDocumentResults=true&ycord=0"
                #print(url2)
                url2 = urlopen(url2).read().decode()
                reg2 = re.compile('a href="(.*?\.htm)')
                reg2 = re.findall(reg2,url2)
                for el in reg2:
                    print(el)
                    #print(el)
                    #li.append(el)
                    reg3 = re.search('hrg(\d*?)\/',el)
                    try:
                        site = urlopen(el).read()
                        text = open("CongressBLAHfolder/"+agen+str(num)+a+str(reg3.groups()[0])+".txt","wb")
                        text.write(site)
                    except Exception as e:
                        print("This didn't work: "+str(e))
                    #pdf.write(bytes(site))
    #print(len(li))

#This cleans the scraped data from gpo_scrape
def re_clean_written():
    for subdir, dirs, files in os.walk("Congressional Hearings TXT/"):
        for file in files:
            print("Working on file...." + str(file))
            f = open(os.path.join(subdir, file), "rb").read().decode('utf-8', 'ignore').encode('cp850',
                                                                                               'ignore').decode(
                'cp850')
            reg2 = re.compile('[JFMASOND][A-Za-z]+? \d{1,2}. \d{4}')

            try:
                date = re.findall(reg2, f)[0].capitalize()
                date = datetime.datetime.strptime(date, '%B %d, %Y')
                date = str(date.year) + "." + str(date.month) + "." + str(date.day)
                print(date)
            except Exception as e:
                print("NO DATE in this file: " + file)

            #This is the big line that I need to check: gets only the relevant stuff from each transcript
            reg = re.compile(
                '\n{1,3} {4}([A-Z][a-z]+\.? [A-Z][a-z]+(?: [A-Z][a-z]+)?\.{1} [A-Z][^\b]*?)\n{1,3} {4,}\[(?:Where|Add)')
            newtext = re.findall(reg, f)
            # print(newtext)

            #Takes out prepared written statements, so there's just actual speech remaining
            try:
                newtext = re.sub(
                    '(\[(?:The opening|The (?:information)? follow|The prepared|Text of)[^\b]+?)(?=\n{1,3} {4}[A-Z][a-z]+\.? [A-Z][a-z]+(?: [A-Z][a-z]+)?\.)',
                    '', newtext[0])
                newtext = re.sub(
                    '((?:O[Pp][Ee][Nn][Ii][Nn][Gg] |P[Rr][Ee][Pp][Aa][Rr][Ee][Dd] )?S[Tt][Aa][Tt][Ee][Mm][Ee][Nn][Tt][Ss]?[^\b]*?\n{2})',
                    '', newtext)
                with open('Congressional Hearings TXT (clean NEW)/' + file[:-4] + '_' + date + '.txt',
                          'a') as fi:
                    fi.write(",".join(reg3) + "\n" + newtext)
            except Exception as e:
                print("ERROR IN SCRAPE: " + file + "\t" + str(e))

#After running re_clean_written, this parses the data out and creates folders for each speaker
def parse_by_speakerdate():
    a = defaultdict(list)
    for subdir, dirs, files in os.walk("Congressional Hearings TXT (clean)/"):
        for file in files:
            print("Working on file...." + str(file))
            f = open(os.path.join(subdir, file), "rb").read().decode('utf-8', 'ignore')
            date = file.split("_")[1][:-4]

            # Load original files, so I can get the names of everyone
            f2 = open("Congressional Hearings TXT/" + file.split("_")[0] + ".txt", "rb").read().decode()

            # Code to get name list from beginning of each file on GPO.gov (need to make sure this gets everyone)
            try:
                reg3 = re.compile('(?: {4,}|\r?\n?)([A-Z]+\.? [A-Z]+\.?(?: [A-Z]+)?),')
                # reg3 = re.compile(' {4,}([A-Z]+ [A-Z]+?),')
                reg3 = re.findall(reg3, f2)
                print(reg3)
            except Exception as e:
                print("SOME ERROR HERE WITH COLLECTING NAMES..." + str(e))

            try:
                newtext = re.split(
                    '\r\n\r?\n? {4,}(?=[A-Z][a-z]+\.? [A-Z][a-z]+(?: [A-Z][a-z]+| \[presiding\])?\.)', f)
                # print(newtext)
                print(len(newtext))
                for line in newtext:
                    b = defaultdict(list)
                    name = line.split(".")[0]
                    # This corrects for the split on the period in Mr. or Mrs. (makes sure it gets their full name)
                    if len(name) < 4:
                        name = ".".join(line.split(".")[:2])

                    name = stringdist_list(name, reg3)

                    text = line.split(".")[1]
                    if len(text) < 15:
                        text = line.split(".", 2)[2]

                    if not os.path.exists('Congressional Hearings - People (new)/' + name + '/'):
                        os.makedirs('Congressional Hearings - People (new)/' + name + '/')

                    # Only download files if they are longer than 100 words (prevents need to use clean_people_dir_words in SVM Practice file)
                    if len(text.split(" ")) > 100:
                        with open('Congressional Hearings - People (new)/' + name + '/' + name + '_' + date + '.txt','a') as fi:
                            fi.write(text + "\n")

                            # print(text)
                            # b[date].append(text)
                            # a[name].append(b)
            except Exception as e:
                print("ERROR IN SCRAPE: " + file + "\t" + str(e))
                # df_dict.tabulate()
                # df_dict.plot()
                # pickle.dump(df_dict,open("FDA Open Meetings Sites/Word Tokenized Dictionary.p","wb"))

#From the gpo.gov Congressional Directory, scrapes the txt file for each member of House/Senate going back to 105th Congress (1997-1998). Saves to GPO Biographies folder.
def gpo_scrape_bio():
    #Pre-downloaded file that just lists state in one column and number of House representatives in the 2nd column
    NumReps = pd.read_csv("Representatives by State.csv")
    #Convert the csv to a dictionary for easier calling of values
    repsdict = NumReps.set_index("State")["NumRep"].to_dict()
    for state in NumReps.State:
        for agen in ["H", "S"]:
            if agen=="H":
                Num = repsdict[state]
            else:
                Num = 2
            for years in ["2016-02-12","2014-02-18","2011-12-01","2009-12-01","2008-08-01","2007-08-09","2006-09-01","2005-07-11","2004-08-01","2004-01-01","2003-11-01","2003-07-11",
                         "2002-10-01","2001-12-07","2000-10-01","2000-02-01","1999-06-15","1997-06-04"]:
                for num in range(1,Num+1):
                    url = "https://www.gpo.gov/fdsys/pkg/CDIR-"+years+"/html/CDIR-"+years+"-"+state+"-"+agen+"-"+str(num)+".htm"
                    print(url)
                    try:
                        url = urlopen(url).read().decode()
                        text = open("GPO Biographies/"+agen+" "+state+" "+str(num)+" "+years+".txt","w")
                        text.write(url)
                    except Exception as e:
                        print("Number of representatives changed in "+state+" in"+years)

#From the files in GPO Biographies folder, pulls out the name, affiliation, education, and year of the txt files using regex (1262 people?)
def gpo_regex_get_name():
    a = defaultdict(list)
    for subdir,dirs,files in os.walk("GPO Biographies/"):
        for file in files:
            f = open(os.path.join(subdir,file),"rb").read().decode('utf-8','ignore')
            name = re.compile(' {4}([A-Z\.]+? [^0-9]*?), ([A-Za-z]{4,})(?:,| |-|;)').findall(f)
            year = re.compile('<title>.*?for the (.*?),').findall(f)
            #reg2 = re.compile('education: ([\s\S]*?); [a-z ]*?: | ')
            f2 = re.sub("\r\n","",f)
            edu = re.compile('((?:[A-Z]\.){2,3},[\s\S]*?);').findall(f2)
            print(name, file, year, edu)
            try:
                if name[0][0] not in a:
                    a[name[0][0]].append(name[0][1]) #name[1] is political affiliation because the txt file was organized in such a way
            except Exception as e:
                print("Problem with name in file: "+file)
            try:
                if file[0]=="H":
                    a[name[0][0]].append(year[0] + " - House")
                if file[0] == "S":
                    a[name[0][0]].append(year[0] + " - Senate")
            except Exception as e:
                print("Problem with year: "+file)
            try:
                a[name[0][0]].extend(edu)
            except Exception as e:
                print("Problem with education: " + file)
    print(a)
    #Suggestion to use json for defaultdict instead of csv (http://codereview.stackexchange.com/questions/30741/writing-defaultdict-to-csv-file)
    json.dump(a,open('GPO Biographies - JSON','w'))
    #pd.DataFrame.from_dict(a, orient='index').to_csv("GPO Biographies - Education1.csv")


#Takes a list of names, searches them on C-SPAN, and extracts the website associated with them - website includes PersonID
def cspan_selenium_getsite():
    ###Create files with each Senator and their full website, including PersonID
    #Load GPO Biographies - JSON and extract the key, which is names of all Congresspeople going back to 1997
    names = json.load(open('GPO Biographies - JSON'))
    names = list(names.keys())
    #This gets rid of middle names and middle initials, so the search is better on C-SPAN
    names = [name.split(" ")[0].title() + " " + name.split(" ")[-1].title() for name in names]

    # Log in with Selenium
    driver = webdriver.Firefox()
    driver.get("http://www.c-span.org")
    login = driver.find_element_by_class_name("my-cspan")
    login.click()
    time.sleep(1)
    user = driver.find_elements_by_id("login")[1]
    user.clear()
    user.send_keys(username)
    pw = driver.find_element_by_id("password")
    pw.clear()
    pw.send_keys(pw)
    clicklogin = driver.find_element_by_id("submit-login")
    clicklogin.click()

    errorlog = []
    for name in names:
        try:
            #Have to wait a bit of time because the website gets screwy and can't find the dropdown menu sometimes
            time.sleep(10)
            openfilter = driver.find_element_by_class_name('selected')
            # openfilter = driver.find_element_by_xpath("//form[@class='search']/fieldset/div/span[@class='carat icon-chevron-down']")
            openfilter.click()
            peoplefilter = driver.find_element_by_xpath('//div[@style]/ul/li[4]')
            time.sleep(0.5)
            peoplefilter.click()
            namesearch = driver.find_element_by_id('global-search')
            namesearch.clear()
            namesearch.send_keys(name)
            clicker = driver.find_element_by_class_name('icon-search')
            clicker.click()

            time.sleep(1.5)
            search = driver.find_elements_by_class_name('thumb')[0]
            search.click()
            source = driver.page_source
            ID = re.compile('personid\[\]=(.*?)"').findall(source)
            print(name,names.index(name),ID)
            with open("C-SPAN PersonID1.txt","a") as f:
                f.write(name+"\t"+ID[0]+"\n")
            if len(ID) > 4:
                errorlog.append(name)
        except Exception as e:
            print("COME BACKKKK AND GET THIS ONE MANUALLY!!!: ", name)
            errorlog.append(name)
    print(errorlog)



#This takes a tab delimited file with name and C-SPAN website, and just simplifies it so it's name and C-SPAN ID (using output from cspan_selenium_getsite
def cspan_selenium_getid():
###Create a file with just Senator's name and personID in separate column
    with open("C-SPAN PersonID.txt") as f:
        f = f.read().splitlines()
        print(f)
        for item in f:
            ID = item.split("=")[-1]
            name = item.split("\t")[0]
            with open("C-SPAN PersonID (simplified).txt","a") as g:
                g.write(name+"\t"+ID+"\n")

#Makes file names the correct case (upper, lower) when matching them in match_name_CongressRecord() function below. Also turns it from
#tab delimited text file into list
def file_to_list_upper(file):
    with open(file,"r",encoding="ISO-8859-1") as f:
        f = f.readlines()
        return([x.split("\t")[0].title() for x in f])

#C-SPAN PersonID file has names and C-SPAN ID. This function takes the person's name and returns their C-SPAN ID
def dict_cspan_id(name):
    with open("C-SPAN PersonID (simplified).txt","r",encoding="Latin1") as f:
        df = pd.Series.from_csv(f,sep="\t",header=None).to_dict()
        return(df[name])

#Match name from Congressional Record to names of spoken word text files, and then get C-SPAN ID
def match_name_CongressRecord():
    allcongrnames = json.load(open('GPO Biographies - JSON'))
    allcongrnameslist = list(allcongrnames.keys())
    #print(file_to_list_upper("C-SPAN PersonID (simplified).txt"))
    #print(len(namelist))

    allcongrnameslist = [name.split(" ")[0]+" "+name.split(" ")[-1] for name in allcongrnameslist]
    #print(namelist)

    #The /media/jemme directory is from my orange external hard drive
    for root,dirs,files in os.walk("/media/jemme/New Volume/Congressional Hearings - People (new)"):
        for file in files:
            name = file.split("_")[0]  # Need to match name with ID
            date = file.split("_")[1][:-4]  # Need in this format: 2015-06-10
            try:
                date = datetime.datetime.strptime(date, "%Y.%m.%d").strftime("%Y-%m-%d")
                #print(name, date)
            except Exception as e:
                print(file + " has a weird file name, I think..." + str(e))

            namematch = difflib.get_close_matches(name,allcongrnameslist,cutoff=.8)

            # The outer function finds the ID based on the name, using the C-SPAN PersonID file. stringdist_list_imperfect compares the name of the file in the folder
            # to the list of names from the C-SPAN PersonID file and returns the name that is closest, which is fed into the outer function to find the ID
            if difflib.get_close_matches(name.title(), file_to_list_upper("C-SPAN PersonID (simplified).txt"),cutoff=.8):
                print(difflib.get_close_matches(name.title(), file_to_list_upper("C-SPAN PersonID (simplified).txt"),cutoff=.8))
                ID = dict_cspan_id(difflib.get_close_matches(name.title(), file_to_list_upper("C-SPAN PersonID (simplified).txt"),cutoff=.8)[0])
                #ID = dict_cspan_id(difflib.get_close_matches(name.title(), file_to_list_upper("C-SPAN PersonID (simplified test).txt")))
                print(name,ID)

#Several functions now add important info to the C-SPAN PersonID file - the below adds the dates each person spoke based on the transcripts
def add_dates():
    with open("C-SPAN PersonID.txt",encoding="Latin1") as f:
        f = f.read().splitlines()
        #f = [item.split("\t")[0] for item in f]
        #print(os.listdir("Congressional Hearings - People (new)"))
        for item in f:
            print(item)
            #This first has to capitalize just the first letter of the transcript names, since they are all caps beforehand
            #and, thus, can't match
            transcriptnames = [name.title() for name in os.listdir("/media/jemme/New Volume/Congressional Hearings - People (new)")]
            transcriptnamesmatch = difflib.get_close_matches(item,transcriptnames)
            if transcriptnamesmatch:
                print(transcriptnamesmatch)
                #Turn the matched name back into all caps after it matches, so that it can find the actual transcript file
                try:
                    dates = os.listdir("/media/jemme/New Volume/Congressional Hearings - People (new)/"+transcriptnamesmatch[0].upper())
                except Exception as e:
                    print(item+" doesn't WORKKKKK!")
                for date in dates:
                    date = date.split("_")[1][:-4].replace(".","-")
                    with open("C-SPAN PersonID and File Dates.txt","a") as outfile:
                        outfile.write(item+"\t"+transcriptnamesmatch[0]+"\t"+date+"\n")

#This is just a helper function used in add_date_month below - it converts dates into the proper format
def set_date(date):
    date = datetime.datetime.strptime(date,"%Y-%m-%d")
    date = datetime.datetime.strftime(date, "%Y-%m-%d")
    return(date)

#Because there weren't corresponding videos for the specific dates in the Congressional Record transcripts,
#this just makes it so you can search a person on C-SPAN for that whole month, not just a specific day.
def add_date_month():
    with open("C-SPAN PersonID and File Dates.txt") as f:
        f = f.read().splitlines()
        for item in f:
            name = item.split("\t")[0]
            ID = item.split("\t")[1]
            nameinfile = item.split("\t")[2]
            try:
                date = item.split("\t")[3]
                datebeg = re.sub("-\d{1,2}$", "-01", date)
                datebeg = set_date(datebeg)
                if date.split("-")[1] in ["9", "4", "6", "11"]:
                    dateend = re.sub("-\d{1,2}$", "-30", date)
                    dateend = set_date(dateend)
                elif date.split("-")[1] in ["1", "3", "5", "7", "8", "10", "12"]:
                    dateend = re.sub("-\d{1,2}$", "-31", date)
                    dateend = set_date(dateend)
                elif date.split("-")[1] == "2":
                    dateend = re.sub("-\d{1,2}$", "-28", date)
                    dateend = set_date(dateend)
                with open("C-SPAN PersonID and File Dates (entire month search)1.txt", "a") as outfile:
                    outfile.write(item + "\t" + datebeg + "\t" + dateend + "\n")
            except Exception as e:
                print("DATE NOT CORRECT: ",date)

#This goes into C-SPAN and adds in the times that each person spoke in each video, so I don't have to download the entire thing
def get_vid():
    driver = webdriver.Firefox()

    with open("C-SPAN PersonID and File Dates (entire month search).txt") as f:
        f = f.read().splitlines()
        for item in f:
            ID = item.split("\t")[1]
            name = item.split("\t")[2]
            date = item.split("\t")[3]
            datebeg = item.split("\t")[4]
            dateend = item.split("\t")[5]

            #Use this code below to get video corresponding to each PersonID and date
            driver.get("http://www.c-span.org/search/?searchtype=Videos&personid[]=" + str(ID) + "&sdate=" + str(datebeg) + "&edate=" + str(dateend))

            try:
                video = driver.find_elements_by_class_name("thumb")[0]
                video.click()

                time.sleep(6)
                html = driver.execute_script("return document.getElementsByTagName('html')[0].innerHTML")

                reg = re.compile('<th>[\s\S]+?time-(.*?)"[\s\S]+?<strong>(.*?)<')
                reg = re.findall(reg,html)

                times = []
                i = 0
                while i < len(reg):
                    if reg[i][1].split(" ")[-1].title() in name:
                        times.append((reg[i][0],reg[i+1][0]))
                    i+=1

                #reg = [tup for tup in reg if tup[1].split(" ")[-1].title() in name]
                print()
                print(driver.current_url,"\n",reg,"\n",times,"\n",name, "\n", ID, "\n", date)

                with open("C-SPAN PersonID and File Dates (entire month search with vid website and time)1.txt","a") as outfile:
                    if times:
                        for tup in times:
                            outfile.write(item+"\t"+driver.current_url+"\t"+tup[0]+"\t"+tup[1]+"\t"+str(f.index(item))+"\n")

            except Exception as e:
                print(str(e))
                # print("There is no video for "+str(name)+"on "+str(date)+".")

            #This actually clicks on the video - make sure rtmpsrv is running BEFORE you even click the thumb link to
            #the video, otherwise it won't work. So, essentially, go to c-span.com, then run ./rtmpsuckredirect.sh
            #from the command line. Then start rtmpsrv. Rtmpsrv has to be running before you click the video thumbnail,
            #not just before you click play.
            flash = driver.find_element_by_id("flashPlayer")
            time.sleep(5)
            ###Below code is not working until Selenium gets updated (https://github.com/SeleniumHQ/selenium/issues/2285)
            ActionChains(driver).move_to_element(flash).click().perform()
            ###Trying javascript clicking
            #driver.execute_script("arguments[0].click();", flash)
            time.sleep(8)


#This cleans the final long list of rtmpdump commands created after running get_vid
#Then, run this file in the Linux command prompt to get all the videos
def rtmp_file():
    with open("C-SPAN PersonID and File Dates (entire month search with vid website and time).txt") as f:
        f = f.read()
        f = re.sub("\nDuplicate request, skipping\.\n\n","\t",f)
        f = f.splitlines()
        f = [line for line in f if line.split(" ")[0].istitle()]

        for line in reversed(f):
            name = line.split("\t")[0].replace(" ","")
            date = line.split("\t")[3].split("-")[:-1]
            date = "-".join(date)
            starttime = line.split("\t")[7]
            if len(line.split("\t"))>10:
                rtmp = line.split("\t")[10].split(" -o ")[0] + " -o " +name + date + "_" + starttime + ".flv"
                with open("CSpanVideos/RTMPdump Cspan Commands.sh", "a") as outfile:
                    outfile.write(rtmp + " -A " + line.split("\t")[7] + " -B " + line.split("\t")[8] + "\n")
            else:
                with open("CSpanVideos/RTMPdump Cspan Commands.sh", "a") as outfile:
                    outfile.write(rtmp[:-4] + line.split("\t")[7] + ".flv" + " -A " + line.split("\t")[7] + " -B " + line.split("\t")[8] + "\n")


                #rtmp = line.split("\t")[10][:-4]+line.split("\t")[7]+".flv"

            #print(line,"\n",rtmp, " -A ", line.split("\t")[7], " -B ", line.split("\t")[8])

            # if len(line.split("\t"))>10:
            #     print(line.split("\t"))
            #     print(line.split("\t"))
            #     print(line," -A ",line.split("\t")[7]," -B ",line.split("\t")[8])
            #     print(line.split("\t")[10]," -A ",line.split("\t")[7]," -B ",line.split("\t")[8])

###LASTLY, once you have the shell file created from rtmp_file, run it from Linux command line.
###First, you need to run rtmpsrv and such...


if __name__ == "__main__":
    #match_name_CongressRecord()
    #add_dates()
    #cspan_selenium_getsite()
    get_vid()
